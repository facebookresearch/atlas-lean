/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union

/-!
# Functional dependencies

Attributes range over a finite type `A`. A functional dependency `X → Y` (`FD.mk X Y`, for
attribute sets `X Y : Finset A`) holds in a relation `r`, given as a set of tuples `A → V`, when
any two tuples of `r` that agree on `X` also agree on `Y` (`FD.HoldsIn`). A set of dependencies
`F` entails `X → Y` (`Entails`) when `X → Y` holds in every relation in which all of `F` holds.

`Derives F f` is derivability with **Armstrong's axioms** (reflexivity, augmentation,
transitivity) from the dependencies in `F`.
* `Derives.sound`: Armstrong's axioms are sound.
* `Derives.union`, `Derives.decompose`, `Derives.pseudotrans`: the derived rules.
* `attrClosure F X` is the attribute-closure algorithm: starting from `X`, repeatedly add the
  right side of every dependency whose left side is already included, until nothing changes.
  `derives_iff_subset_attrClosure`: `F` derives `X → Y` exactly when `Y ⊆ attrClosure F X`, so
  the algorithm computes `X⁺` (`mem_attrClosure`) and decides derivability.
* `holdsIn_closureWitnessRelation`: the relation of at most two tuples that agree exactly on
  `attrClosure F X` satisfies `F` (the usual witness in the completeness proof; it is not an
  Armstrong relation for `F` in the sense of satisfying exactly the consequences of `F`).
* `derives_iff_entails` (**Armstrong's theorem**): the axioms are sound and complete.
  `derives_of_forall_two_tuple` is the sharper completeness statement: a dependency holding in
  every two-tuple `Bool`-valued relation that satisfies `F` is derivable.

Keys: `IsSuperkey F K` (`K` determines all attributes) and `IsCandidateKey F K` (a minimal
superkey).
* `isSuperkey_iff_attrClosure` and `isCandidateKey_iff` reduce both to closure computations;
  `IsSuperkey.eq_of_agree` is the meaning of a superkey in every relation satisfying `F`.
* `findKey F l` removes the attributes of `l` one at a time from the full attribute set,
  dropping each one whose removal leaves a superkey; `findKey_isCandidateKey`: when `l` lists all
  attributes it returns a candidate key. `exists_isCandidateKey_subset`: every superkey contains
  a candidate key.

## References

* W. W. Armstrong, *Dependency structures of data base relationships*, IFIP Congress 1974.
* S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995,
  Section 8.2 (functional and key dependencies).
* J. D. Ullman, *Principles of Database and Knowledge-Base Systems*, Vol. I, Computer Science
  Press, 1988, Chapter 7 (Armstrong's axioms and the attribute-closure algorithm).
-/

@[expose] public section

namespace Cslib.Databases

/-- A functional dependency `lhs → rhs` between sets of attributes. -/
structure FD (A : Type*) where
  /-- The determining attributes. -/
  lhs : Finset A
  /-- The determined attributes. -/
  rhs : Finset A
deriving DecidableEq

variable {A : Type*}

namespace FD

/-- `f` holds in the relation `r`: tuples of `r` that agree on `f.lhs` agree on `f.rhs`. -/
def HoldsIn {V : Type*} (f : FD A) (r : Set (A → V)) : Prop :=
  ∀ t ∈ r, ∀ u ∈ r, (∀ a ∈ f.lhs, t a = u a) → ∀ a ∈ f.rhs, t a = u a

end FD

/-- Every dependency of `F` holds in `r`. -/
def Satisfies {V : Type*} (r : Set (A → V)) (F : Finset (FD A)) : Prop := ∀ f ∈ F, f.HoldsIn r

/-- `F` entails `f`: `f` holds in every relation (with values in any type) satisfying `F`. -/
def Entails (F : Finset (FD A)) (f : FD A) : Prop :=
  ∀ (V : Type) (r : Set (A → V)), Satisfies r F → f.HoldsIn r

variable [DecidableEq A]

/-- Derivability from `F` with Armstrong's axioms. -/
inductive Derives (F : Finset (FD A)) : FD A → Prop
  /-- The dependencies of `F` are derivable. -/
  | mem {f : FD A} : f ∈ F → Derives F f
  /-- Reflexivity: `X → Y` whenever `Y ⊆ X`. -/
  | refl {X Y : Finset A} : Y ⊆ X → Derives F ⟨X, Y⟩
  /-- Augmentation: from `X → Y` derive `X ∪ Z → Y ∪ Z`. -/
  | augment {X Y : Finset A} (Z : Finset A) : Derives F ⟨X, Y⟩ → Derives F ⟨X ∪ Z, Y ∪ Z⟩
  /-- Transitivity: from `X → Y` and `Y → Z` derive `X → Z`. -/
  | trans {X Y Z : Finset A} : Derives F ⟨X, Y⟩ → Derives F ⟨Y, Z⟩ → Derives F ⟨X, Z⟩

namespace Derives

variable {F : Finset (FD A)}

/-- **Armstrong's axioms are sound**: a derivable dependency holds in every relation satisfying
`F`. -/
theorem sound {V : Type*} {r : Set (A → V)} (hr : Satisfies r F) :
    ∀ {f : FD A}, Derives F f → f.HoldsIn r
  | _, mem h => hr _ h
  | _, refl hYX => fun _ _ _ _ h a ha => h a (hYX ha)
  | _, augment Z h => fun t ht u hu hagree a ha => by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact sound hr h t ht u hu (fun b hb => hagree b (Finset.mem_union_left _ hb)) a ha
    · exact hagree a (Finset.mem_union_right _ ha)
  | _, trans h₁ h₂ => fun t ht u hu hagree =>
    sound hr h₂ t ht u hu (sound hr h₁ t ht u hu hagree)

/-- The decomposition rule: from `X → Y` derive `X → Z` for `Z ⊆ Y`. -/
theorem decompose {X Y Z : Finset A} (h : Derives F ⟨X, Y⟩) (hZ : Z ⊆ Y) : Derives F ⟨X, Z⟩ :=
  trans h (refl hZ)

/-- The union rule: from `X → Y` and `X → Z` derive `X → Y ∪ Z`. -/
theorem union {X Y Z : Finset A} (hY : Derives F ⟨X, Y⟩) (hZ : Derives F ⟨X, Z⟩) :
    Derives F ⟨X, Y ∪ Z⟩ := by
  have h₁ := augment X hZ
  rw [Finset.union_self, Finset.union_comm] at h₁
  have h₂ := augment Z hY
  exact trans h₁ h₂

/-- The pseudotransitivity rule: from `X → Y` and `Y ∪ W → Z` derive `X ∪ W → Z`. -/
theorem pseudotrans {X Y W Z : Finset A} (h₁ : Derives F ⟨X, Y⟩) (h₂ : Derives F ⟨Y ∪ W, Z⟩) :
    Derives F ⟨X ∪ W, Z⟩ :=
  trans (augment W h₁) h₂

/-- A dependency `X → Y` gives `X → X ∪ Y`. -/
theorem union_left {X Y : Finset A} (h : Derives F ⟨X, Y⟩) : Derives F ⟨X, X ∪ Y⟩ :=
  union (refl subset_rfl) h

private theorem biUnion {ι : Type*} {X : Finset A} (s : Finset ι)
    (g : ι → Finset A) (h : ∀ i ∈ s, Derives F ⟨X, g i⟩) : Derives F ⟨X, s.biUnion g⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact refl (Finset.empty_subset _)
  | insert i s hi ih =>
    rw [Finset.biUnion_insert]
    exact union (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Derives

/-! ### The attribute-closure algorithm -/

/-- One round of the closure algorithm: add the right side of every dependency whose left side
is contained in `Y`. -/
def closureStep (F : Finset (FD A)) (Y : Finset A) : Finset A :=
  Y ∪ (F.filter fun f => f.lhs ⊆ Y).biUnion FD.rhs

/-- Repeat `closureStep` until nothing changes, for at most `n` rounds. -/
def closureLoop (F : Finset (FD A)) : ℕ → Finset A → Finset A
  | 0, Y => Y
  | n + 1, Y => if closureStep F Y = Y then Y else closureLoop F n (closureStep F Y)

variable [Fintype A]

/-- The **attribute closure** `X⁺` of `X` under `F`, computed by the closure algorithm; the
number of rounds is bounded by the number of attributes. -/
def attrClosure (F : Finset (FD A)) (X : Finset A) : Finset A :=
  closureLoop F (Fintype.card A) X

omit [Fintype A] in
private theorem subset_closureStep (F : Finset (FD A)) (Y : Finset A) : Y ⊆ closureStep F Y :=
  Finset.subset_union_left

omit [Fintype A] in
private theorem subset_closureLoop (F : Finset (FD A)) :
    ∀ (n : ℕ) (Y : Finset A), Y ⊆ closureLoop F n Y
  | 0, _ => subset_rfl
  | n + 1, Y => by
    simp only [closureLoop]
    split_ifs
    · exact subset_rfl
    · exact (subset_closureStep F Y).trans (subset_closureLoop F n _)

omit [Fintype A] in
private theorem derives_closureStep {F : Finset (FD A)} {X Y : Finset A}
    (h : Derives F ⟨X, Y⟩) : Derives F ⟨X, closureStep F Y⟩ := by
  refine h.union (Derives.biUnion _ _ fun g hg => ?_)
  obtain ⟨hgF, hgY⟩ := Finset.mem_filter.mp hg
  exact Derives.trans (h.decompose hgY) (Derives.mem hgF)

omit [Fintype A] in
private theorem derives_closureLoop {F : Finset (FD A)} {X : Finset A} :
    ∀ (n : ℕ) {Y : Finset A}, Derives F ⟨X, Y⟩ → Derives F ⟨X, closureLoop F n Y⟩
  | 0, _, h => h
  | n + 1, Y, h => by
    simp only [closureLoop]
    split_ifs
    · exact h
    · exact derives_closureLoop n (derives_closureStep h)

/-- After enough rounds the loop reaches a fixed point of `closureStep`. -/
private theorem closureStep_closureLoop (F : Finset (FD A)) :
    ∀ (n : ℕ) (Y : Finset A), Fintype.card A ≤ n + Y.card →
      closureStep F (closureLoop F n Y) = closureLoop F n Y
  | 0, Y, h => by
    have hY : Y = Finset.univ := Finset.eq_univ_of_card Y (le_antisymm (Finset.card_le_univ Y)
      (by simpa using h))
    subst hY
    exact Finset.eq_univ_iff_forall.mpr fun a => subset_closureStep F _ (Finset.mem_univ a)
  | n + 1, Y, h => by
    simp only [closureLoop]
    split_ifs with hfix
    · exact hfix
    · have hlt : Y.card < (closureStep F Y).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_closureStep F Y,
          fun h => hfix h.symm⟩)
      exact closureStep_closureLoop F n _ (by omega)

/-- The closure is a fixed point of a closure round. -/
theorem closureStep_attrClosure (F : Finset (FD A)) (X : Finset A) :
    closureStep F (attrClosure F X) = attrClosure F X :=
  closureStep_closureLoop F _ X (Nat.le_add_right _ _)

theorem subset_attrClosure (F : Finset (FD A)) (X : Finset A) : X ⊆ attrClosure F X :=
  subset_closureLoop F _ X

/-- The closure is closed under the dependencies of `F`. -/
theorem rhs_subset_attrClosure {F : Finset (FD A)} {X : Finset A} {g : FD A} (hg : g ∈ F)
    (hlhs : g.lhs ⊆ attrClosure F X) : g.rhs ⊆ attrClosure F X := by
  rw [← closureStep_attrClosure F X]
  intro a ha
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr
    ⟨hg, hlhs⟩, ha⟩)

theorem derives_attrClosure (F : Finset (FD A)) (X : Finset A) :
    Derives F ⟨X, attrClosure F X⟩ :=
  derives_closureLoop _ (Derives.refl subset_rfl)

/-- The closure witness for `X`: at most two tuples, which agree exactly on `attrClosure F X`
(they coincide when the closure is everything). -/
def closureWitnessRelation (F : Finset (FD A)) (X : Finset A) : Finset (A → Bool) :=
  {fun _ => true, fun a => decide (a ∈ attrClosure F X)}

/-- The closure witness satisfies `F`. -/
theorem holdsIn_closureWitnessRelation (F : Finset (FD A)) (X : Finset A) :
    Satisfies (↑(closureWitnessRelation F X) : Set (A → Bool)) F := by
  have key : ∀ g ∈ F, (∀ a ∈ g.lhs, true = decide (a ∈ attrClosure F X)) →
      ∀ a ∈ g.rhs, true = decide (a ∈ attrClosure F X) := fun g hg h a ha => by
    have hsub : g.lhs ⊆ attrClosure F X := fun b hb => by simpa using h b hb
    simpa using rhs_subset_attrClosure hg hsub ha
  intro g hg t ht u hu hagree
  simp only [closureWitnessRelation, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ht hu
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
  · exact fun _ _ => rfl
  · exact key g hg hagree
  · exact fun a ha => (key g hg (fun b hb => (hagree b hb).symm) a ha).symm
  · exact fun _ _ => rfl

/-- **The closure algorithm decides derivability**: `F` derives `X → Y` exactly when
`Y ⊆ attrClosure F X`. -/
theorem derives_iff_subset_attrClosure {F : Finset (FD A)} {X Y : Finset A} :
    Derives F ⟨X, Y⟩ ↔ Y ⊆ attrClosure F X := by
  constructor
  · intro h a ha
    have := h.sound (holdsIn_closureWitnessRelation F X) (fun _ => true)
      (by simp [closureWitnessRelation]) (fun a => decide (a ∈ attrClosure F X))
      (by simp [closureWitnessRelation])
      (fun b hb => by simpa using subset_attrClosure F X hb) a ha
    simpa using this
  · exact (derives_attrClosure F X).decompose

/-- **The closure algorithm computes `X⁺`**: its result is the set of attributes `a` with
`X → a` derivable. -/
theorem mem_attrClosure {F : Finset (FD A)} {X : Finset A} {a : A} :
    a ∈ attrClosure F X ↔ Derives F ⟨X, {a}⟩ := by
  rw [derives_iff_subset_attrClosure, Finset.singleton_subset_iff]

instance (F : Finset (FD A)) (f : FD A) : Decidable (Derives F f) :=
  decidable_of_iff (f.rhs ⊆ attrClosure F f.lhs) derives_iff_subset_attrClosure.symm

omit [Fintype A] in
/-- **Completeness**, in its sharp form: a dependency that holds in every two-tuple `Bool`-valued
relation satisfying `F` is derivable. -/
theorem derives_of_forall_two_tuple [Finite A] {F : Finset (FD A)} {f : FD A}
    (h : ∀ r : Finset (A → Bool), r.card ≤ 2 → Satisfies (↑r : Set (A → Bool)) F →
      f.HoldsIn (↑r : Set (A → Bool))) : Derives F f := by
  cases nonempty_fintype A
  obtain ⟨X, Y⟩ := f
  rw [derives_iff_subset_attrClosure]
  intro a ha
  have := h (closureWitnessRelation F X) (Finset.card_le_two) (holdsIn_closureWitnessRelation F X)
    (fun _ => true) (by simp [closureWitnessRelation]) (fun a => decide (a ∈ attrClosure F X))
    (by simp [closureWitnessRelation]) (fun b hb => by simpa using subset_attrClosure F X hb) a ha
  simpa using this

omit [Fintype A] in
/-- **Armstrong's theorem**: Armstrong's axioms are sound and complete for functional
dependencies. -/
theorem derives_iff_entails [Finite A] {F : Finset (FD A)} {f : FD A} :
    Derives F f ↔ Entails F f :=
  ⟨fun h _ _ hr => h.sound hr, fun h => derives_of_forall_two_tuple fun r _ hr => h Bool r hr⟩

/-! ### Keys -/

/-- `K` is a superkey: it determines every attribute. -/
def IsSuperkey (F : Finset (FD A)) (K : Finset A) : Prop := Derives F ⟨K, Finset.univ⟩

/-- `K` is a candidate key: a superkey none of whose proper subsets is a superkey. -/
def IsCandidateKey (F : Finset (FD A)) (K : Finset A) : Prop :=
  IsSuperkey F K ∧ ∀ K' ⊂ K, ¬ IsSuperkey F K'

theorem isSuperkey_iff_attrClosure {F : Finset (FD A)} {K : Finset A} :
    IsSuperkey F K ↔ attrClosure F K = Finset.univ := by
  rw [IsSuperkey, derives_iff_subset_attrClosure, Finset.univ_subset_iff]

instance (F : Finset (FD A)) (K : Finset A) : Decidable (IsSuperkey F K) :=
  decidable_of_iff _ isSuperkey_iff_attrClosure.symm

/-- Supersets of superkeys are superkeys. -/
theorem IsSuperkey.mono {F : Finset (FD A)} {K K' : Finset A} (h : IsSuperkey F K)
    (hKK' : K ⊆ K') : IsSuperkey F K' :=
  Derives.trans (Derives.refl hKK') h

/-- In a relation satisfying `F`, two tuples that agree on a superkey are equal. -/
theorem IsSuperkey.eq_of_agree {V : Type*} {F : Finset (FD A)} {K : Finset A}
    (h : IsSuperkey F K) {r : Set (A → V)} (hr : Satisfies r F) {t u : A → V} (ht : t ∈ r)
    (hu : u ∈ r) (hagree : ∀ a ∈ K, t a = u a) : t = u :=
  funext fun a => h.sound hr t ht u hu hagree a (Finset.mem_univ a)

/-- A candidate key is a superkey from which no single attribute can be removed. -/
theorem isCandidateKey_iff {F : Finset (FD A)} {K : Finset A} :
    IsCandidateKey F K ↔ IsSuperkey F K ∧ ∀ a ∈ K, ¬ IsSuperkey F (K.erase a) := by
  constructor
  · rintro ⟨hK, hmin⟩
    exact ⟨hK, fun a ha => hmin _ (Finset.erase_ssubset ha)⟩
  · rintro ⟨hK, hmin⟩
    refine ⟨hK, fun K' hK' hsk => ?_⟩
    obtain ⟨a, haK, haK'⟩ := Finset.exists_of_ssubset hK'
    exact hmin a haK (hsk.mono fun b hb => Finset.mem_erase.mpr
      ⟨fun hba => haK' (hba ▸ hb), hK'.subset hb⟩)

instance (F : Finset (FD A)) (K : Finset A) : Decidable (IsCandidateKey F K) :=
  decidable_of_iff _ isCandidateKey_iff.symm

/-- Remove the attributes of `l` from `K` one at a time, dropping each one whose removal
leaves a superkey. -/
def shrinkKey (F : Finset (FD A)) : List A → Finset A → Finset A
  | [], K => K
  | a :: l, K =>
    shrinkKey F l (if attrClosure F (K.erase a) = Finset.univ then K.erase a else K)

/-- `findKey F l`: shrink the full attribute set along the list `l`. -/
def findKey (F : Finset (FD A)) (l : List A) : Finset A := shrinkKey F l Finset.univ

private theorem shrinkKey_spec (F : Finset (FD A)) :
    ∀ (l : List A) (K : Finset A), IsSuperkey F K →
      IsSuperkey F (shrinkKey F l K) ∧ shrinkKey F l K ⊆ K ∧
        ∀ a ∈ l, a ∈ shrinkKey F l K → ¬ IsSuperkey F ((shrinkKey F l K).erase a)
  | [], K, hK => ⟨hK, subset_rfl, fun _ ha => absurd ha List.not_mem_nil⟩
  | a :: l, K, hK => by
    set K₁ := if attrClosure F (K.erase a) = Finset.univ then K.erase a else K with hK₁
    have hK₁sk : IsSuperkey F K₁ := by
      rw [hK₁]
      split_ifs with h
      · exact isSuperkey_iff_attrClosure.mpr h
      · exact hK
    have hK₁sub : K₁ ⊆ K := by
      rw [hK₁]
      split_ifs
      · exact Finset.erase_subset a K
      · exact subset_rfl
    obtain ⟨hR, hRsub, hRmin⟩ := shrinkKey_spec F l K₁ hK₁sk
    refine ⟨hR, hRsub.trans hK₁sub, fun b hb hbR => ?_⟩
    simp only [shrinkKey] at hbR ⊢
    rcases List.mem_cons.mp hb with rfl | hb
    · intro hsk
      have hbK₁ : b ∈ K₁ := hRsub hbR
      rw [hK₁] at hbK₁
      split_ifs at hbK₁ with h
      · exact Finset.notMem_erase b K hbK₁
      · exact h (isSuperkey_iff_attrClosure.mp (hsk.mono (Finset.erase_subset_erase b
          (hRsub.trans hK₁sub))))
    · exact hRmin b hb hbR

/-- When `l` lists every attribute, `findKey F l` is a candidate key. -/
theorem findKey_isCandidateKey (F : Finset (FD A)) {l : List A} (hl : ∀ a, a ∈ l) :
    IsCandidateKey F (findKey F l) := by
  obtain ⟨hR, -, hRmin⟩ := shrinkKey_spec F l Finset.univ (Derives.refl subset_rfl)
  exact isCandidateKey_iff.mpr ⟨hR, fun a ha => hRmin a (hl a) ha⟩

/-- Every superkey contains a candidate key. -/
theorem exists_isCandidateKey_subset {F : Finset (FD A)} {K : Finset A} (hK : IsSuperkey F K) :
    ∃ K' ⊆ K, IsCandidateKey F K' := by
  obtain ⟨hR, hRsub, hRmin⟩ := shrinkKey_spec F Finset.univ.toList K hK
  exact ⟨_, hRsub, isCandidateKey_iff.mpr ⟨hR, fun a ha => hRmin a (by simp) ha⟩⟩

end Cslib.Databases
