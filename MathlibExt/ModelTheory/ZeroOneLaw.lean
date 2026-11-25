/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ModelTheory.LabelledStructureCount
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.ModelTheory.PartialEquiv
import Mathlib.ModelTheory.Satisfiability

/-!
# The zero-one law for first-order logic

For a finite relational vocabulary, every first-order sentence is either almost surely true
or almost surely false on labelled finite structures: the proportion of structures on
`{1, …, n}` satisfying it converges to `0` or to `1` (Glebskii, Kogan, Liogon'kii and Talanov
1969; Fagin 1976). The proportion is `FirstOrder.Language.satFraction`. The main result,
`MathlibExt.ModelTheory.ZeroOneLawWanted.zero_one_law`, proves this law.

The hypotheses are those of the classical statement: no function or constant symbols
(`L.IsRelational`), finitely many relation symbols (`Finite L.Symbols`), and no relation
symbol of arity `0` (`IsEmpty (L.Relations 0)`). The last one is necessary: a nullary
relation symbol `P` is a propositional constant, true in exactly half of the structures on
every domain, so the sentence `P` has limiting proportion `1/2`.

## Proof outline

* An *atom* over a type `α` is a relation symbol together with a tuple of elements of `α`. For
  `k : ℕ` and a predicate `D` on the atoms over `Fin (k + 1)`, the extension axiom for `D` says
  that any `k` distinct elements whose atomic diagram is the restriction of `D` to `Fin k` have a
  further element with which their atomic diagram is `D`. It is a first-order sentence because
  there are finitely many relation symbols.
* Fix distinct `x₁, …, x_k` in `Fin n`. The atoms that involve a candidate `y` and the `xᵢ` are
  disjoint for different candidates, so in a uniformly random structure the `n - k` candidates
  fail independently, each with probability `1 - 2 ^ (-c)`, where `c` is the number of atoms
  over `Fin (k + 1)` involving the last element. Hence an extension axiom fails in a proportion
  at most `n ^ k * (1 - 2 ^ (-c)) ^ (n - k)` of the structures on `Fin n`, which tends to `0`.
* The theory `T` of all extension axioms is therefore finitely satisfiable, hence satisfiable by
  compactness. Its models are infinite, and two countable models are isomorphic by the
  back-and-forth argument `FirstOrder.Language.equiv_between_cg`, whose steps are given by the
  extension axioms; it starts from the empty partial isomorphism, which needs that no relation
  symbol is nullary. By the Łoś–Vaught test `Cardinal.Categorical.isComplete`, `T` is complete.
* Given a sentence `φ`, the theory `T` proves `φ` or `∼φ`, and by compactness finitely many
  extension axioms prove it. The proportion of structures on `Fin n` satisfying it is then at
  least one minus the sum of the proportions in which these axioms fail, so it tends to `1`.

## Implementation notes

The theorem keeps the full name it had in the former wanted module, so its namespace still reads
`ZeroOneLawWanted`. All auxiliary declarations are private.

## References

* Y. V. Glebskii, D. I. Kogan, M. I. Liogon'kii and V. A. Talanov, "Range and degree of
  realizability of formulas in the restricted predicate calculus", *Kibernetika* 2 (1969),
  17-28.
* R. Fagin, "Probabilities on finite models", *J. Symbolic Logic* 41 (1976), 50-58.
* P. G. Kolaitis and M. Y. Vardi, "0-1 laws for fragments of existential second-order logic:
  a survey", MFCS 2000, LNCS 1893, 84-98, Section 1 (statement of the law).
-/

@[expose] public section

namespace MathlibExt.ModelTheory.ZeroOneLawWanted

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Filter Topology

universe u v w w'

section Helpers

variable {L : Language.{u, v}}

/-- Atoms over `α`: a relation symbol with a tuple of elements of `α`. -/
private abbrev Atom (L : Language.{u, v}) (α : Type w) : Type (max v w) :=
  Σ p : (Σ l, L.Relations l), Fin p.1 → α

/-- Relabel the elements of an atom. -/
private def Atom.map {α : Type w} {β : Type w'} (f : α → β) (a : Atom L α) : Atom L β :=
  ⟨a.1, f ∘ a.2⟩

/-- The atomic diagram of a map into a structure. -/
private def diag {M : Type w} [L.Structure M] {α : Type w'} (e : α → M) (a : Atom L α) : Prop :=
  RelMap a.1.2 (e ∘ a.2)

/-- The diagram of a composite is the diagram pulled back along the relabelling of atoms. -/
private theorem diag_comp {M : Type w} [L.Structure M] {α β : Type*} (e : β → M) (f : α → β) :
    diag (L := L) (e ∘ f) = diag e ∘ Atom.map f := rfl

private theorem finite_relSymbols [Finite L.Symbols] : Finite (Σ l, L.Relations l) :=
  Finite.of_injective (β := L.Symbols) Sum.inr Sum.inr_injective

/-- The atomic formula of an atom on bound variables. -/
private def lit {m : ℕ} (a : Atom L (Fin m)) : L.BoundedFormula Empty m :=
  a.1.2.boundedFormula fun i => &(a.2 i)

private theorem realize_lit {M : Type w} [L.Structure M] {m : ℕ} (a : Atom L (Fin m))
    (v : Empty → M) (xs : Fin m → M) : (lit a).Realize v xs ↔ diag xs a :=
  Iff.rfl

/-- The diagram formula of `D`. -/
private noncomputable def diagFormula [Finite L.Symbols] {m : ℕ} (D : Atom L (Fin m) → Prop) :
    L.BoundedFormula Empty m :=
  haveI := finite_relSymbols (L := L)
  (BoundedFormula.iInf fun a : {a // D a} => lit a.1) ⊓
    BoundedFormula.iInf fun a : {a // ¬ D a} => ∼(lit a.1)

private theorem realize_diagFormula [Finite L.Symbols] {M : Type w} [L.Structure M] {m : ℕ}
    (D : Atom L (Fin m) → Prop) (v : Empty → M) (xs : Fin m → M) :
    (diagFormula D).Realize v xs ↔ diag xs = D := by
  simp only [diagFormula, BoundedFormula.realize_inf, BoundedFormula.realize_iInf,
    BoundedFormula.realize_not, realize_lit, Subtype.forall]
  constructor
  · rintro ⟨h1, h2⟩
    funext a
    exact propext ⟨fun h => by_contra fun h' => h2 a h' h, h1 a⟩
  · rintro rfl
    exact ⟨fun _ h => h, fun _ h => h⟩

/-- Distinctness of the bound variables. -/
private noncomputable def distinctFormula (m : ℕ) : L.BoundedFormula Empty m :=
  BoundedFormula.iInf fun p : {p : Fin m × Fin m // p.1 ≠ p.2} => ∼((&p.1.1).bdEqual &p.1.2)

private theorem realize_distinctFormula {M : Type w} [L.Structure M] (m : ℕ) (v : Empty → M)
    (xs : Fin m → M) : (distinctFormula (L := L) m).Realize v xs ↔ Function.Injective xs := by
  simp only [distinctFormula, BoundedFormula.realize_iInf, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, Subtype.forall, Prod.forall]
  exact ⟨fun h i j hij => by_contra fun hne => h i j hne hij, fun h i j hne hij => hne (h hij)⟩

/-- The last bound variable differs from the others. -/
private noncomputable def newFormula (k : ℕ) : L.BoundedFormula Empty (k + 1) :=
  BoundedFormula.iInf fun i : Fin k => ∼((&(Fin.last k)).bdEqual &(Fin.castSucc i))

private theorem realize_newFormula {M : Type w} [L.Structure M] (k : ℕ) (v : Empty → M)
    (xs : Fin (k + 1) → M) :
    (newFormula (L := L) k).Realize v xs ↔ ∀ i : Fin k, xs (Fin.last k) ≠ xs i.castSucc := by
  simp [newFormula]

/-- The extension axiom. -/
private noncomputable def extAxiom [Finite L.Symbols] (k : ℕ) (D : Atom L (Fin (k + 1)) → Prop) :
    L.Sentence :=
  ((distinctFormula k ⊓ diagFormula (D ∘ Atom.map Fin.castSucc)).imp
    (BoundedFormula.ex (newFormula k ⊓ diagFormula D))).alls

/-- A structure satisfies the extension axiom for `D` when every injective `k`-tuple with the
diagram of `D` on `Fin k` extends, by an element outside it, to a tuple with diagram `D`. -/
private theorem realize_extAxiom [Finite L.Symbols] {M : Type w} [L.Structure M] (k : ℕ)
    (D : Atom L (Fin (k + 1)) → Prop) :
    M ⊨ extAxiom k D ↔ ∀ x : Fin k → M, Function.Injective x →
      diag x = D ∘ Atom.map Fin.castSucc →
      ∃ y : M, (∀ i, y ≠ x i) ∧ diag (Fin.snoc x y : Fin (k + 1) → M) = D := by
  rw [Sentence.Realize, extAxiom, BoundedFormula.realize_alls]
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf, realize_distinctFormula,
    realize_diagFormula, BoundedFormula.realize_ex, realize_newFormula, Fin.snoc_last,
    Fin.snoc_castSucc, and_imp]

/-! ### Counting -/

/-- Structures on `M` are predicates on atoms. -/
private def structureEquiv [L.IsRelational] (M : Type w) : L.Structure M ≃ (Atom L M → Prop) where
  toFun S a := S.RelMap a.1.2 a.2
  invFun ρ := { funMap := fun f => isEmptyElim f, RelMap := fun R t => ρ ⟨⟨_, R⟩, t⟩ }
  left_inv S := by
    rcases S with ⟨f, r⟩
    have hf : @f = fun _ g => isEmptyElim g := by
      funext _ g
      exact isEmptyElim g
    subst hf
    rfl
  right_inv ρ := rfl

/-- Restriction along an injective map `G` sends the uniform distribution on `ι → Prop` to the
uniform distribution on `β → Prop`: each fibre has `2 ^ (|ι| - |β|)` elements. -/
private theorem card_comp_injective {ι β : Type*} [Finite ι] {G : β → ι} (hG : Function.Injective G)
    (P : (β → Prop) → Prop) :
    Nat.card {ρ : ι → Prop // P (ρ ∘ G)} * 2 ^ Nat.card β =
      Nat.card {τ : β → Prop // P τ} * 2 ^ Nat.card ι := by
  classical
  have : Finite β := Finite.of_injective G hG
  let E : (ι → Prop) ≃ (β → Prop) × (↥(Set.range G)ᶜ → Prop) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ Set.range G) (fun _ => Prop)).trans
      (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective G hG).symm (Equiv.refl Prop))
        (Equiv.refl _))
  have e : {ρ : ι → Prop // P (ρ ∘ G)} ≃ {τ : β → Prop // P τ} × (↥(Set.range G)ᶜ → Prop) :=
    (E.subtypeEquiv (p := fun ρ => P (ρ ∘ G)) (q := fun s => P s.1) fun _ => by rfl).trans
      Equiv.prodSubtypeFstEquivSubtypeProd
  have hC : Nat.card ↥(Set.range G)ᶜ + Nat.card β = Nat.card ι := by
    rw [Nat.card_coe_set_eq, ← Nat.card_range_of_injective hG, Nat.card_coe_set_eq,
      Set.ncard_compl_add_ncard]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Prop),
    Fintype.card_prop, mul_assoc, ← pow_add, hC]

/-- The number of predicates on `J × K` whose restriction to each fibre `{j} × K` differs from a
prescribed predicate. -/
private theorem card_forall_exists_ne {J K : Type*} [Finite J] [Finite K] (a : J → K → Prop) :
    Nat.card {τ : J × K → Prop // ∀ j, ∃ κ, τ (j, κ) ≠ a j κ} =
      (2 ^ Nat.card K - 1) ^ Nat.card J := by
  classical
  have := Fintype.ofFinite J
  have e : {τ : J × K → Prop // ∀ j, ∃ κ, τ (j, κ) ≠ a j κ} ≃
      ∀ j, ↥({a j}ᶜ : Set (K → Prop)) :=
    ((Equiv.curry J K Prop).subtypeEquiv (q := fun σ => ∀ j, σ j ∈ ({a j}ᶜ : Set (K → Prop)))
      fun τ => by simp [Function.ne_iff]).trans
      (Equiv.subtypePiEquivPi (p := fun j σ => σ ∈ ({a j}ᶜ : Set (K → Prop))))
  have hc : ∀ j, Nat.card ↥({a j}ᶜ : Set (K → Prop)) = 2 ^ Nat.card K - 1 := fun j => by
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop]
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [hc, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- Atoms on `Fin (k + 1)` whose tuple uses the last element. -/
private abbrev NewAtom (L : Language.{u, v}) (k : ℕ) : Type v :=
  {a : Atom L (Fin (k + 1)) // ∃ i, a.2 i = Fin.last k}

/-- Relabelling the new atoms along `Fin.snoc x y`, for `y` outside the range of `x`, is
injective in the pair `(y, κ)`. -/
private theorem injective_map_snoc {n k : ℕ} {x : Fin k → Fin n} (hx : Function.Injective x) :
    Function.Injective fun p : {y : Fin n // y ∉ Set.range x} × NewAtom L k =>
      Atom.map (Fin.snoc x p.1.1 : Fin (k + 1) → Fin n) p.2.1 := by
  rintro ⟨⟨y, hy⟩, ⟨⟨p, t⟩, i, hi⟩⟩ ⟨⟨y', hy'⟩, ⟨⟨p', t'⟩, i', hi'⟩⟩ h
  simp only [Atom.map, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  replace h := eq_of_heq h
  dsimp only at hi
  obtain rfl : y = y' := by
    have h' := congrFun h i
    simp only [Function.comp_apply, hi, Fin.snoc_last] at h'
    rcases Fin.eq_castSucc_or_eq_last (t' i) with ⟨m, hm⟩ | hm
    · rw [hm, Fin.snoc_castSucc] at h'
      exact absurd ⟨m, h'.symm⟩ hy
    · rwa [hm, Fin.snoc_last] at h'
  obtain rfl : t = t' := funext fun j => Fin.snoc_injective_of_injective hx hy (congrFun h j)
  rfl

/-- If a predicate `ρ` on atoms of `Fin n` agrees with `D` on the atoms of the range of `x` but
no `y` outside that range realizes `D` together with `x`, then for every such `y` some new atom
disagrees. -/
private theorem exists_newAtom_ne {n k : ℕ} {x : Fin k → Fin n} {D : Atom L (Fin (k + 1)) → Prop}
    {ρ : Atom L (Fin n) → Prop} (h1 : ρ ∘ Atom.map x = D ∘ Atom.map Fin.castSucc)
    (h2 : ∀ y, (∀ i, y ≠ x i) → ρ ∘ Atom.map (Fin.snoc x y : Fin (k + 1) → Fin n) ≠ D)
    (y : Fin n) (hy : y ∉ Set.range x) :
    ∃ κ : NewAtom L k, ρ (Atom.map (Fin.snoc x y : Fin (k + 1) → Fin n) κ.1) ≠ D κ.1 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp (h2 y fun i h => hy ⟨i, h.symm⟩)
  by_cases hlast : ∃ i, a.2 i = Fin.last k
  · exact ⟨⟨a, hlast⟩, ha⟩
  simp only [not_exists] at hlast
  let a' : Atom L (Fin k) := ⟨a.1, fun i => (a.2 i).castPred (hlast i)⟩
  have ha' : Atom.map Fin.castSucc a' = a :=
    Sigma.ext rfl (heq_of_eq (funext fun i => Fin.castSucc_castPred (a.2 i) (hlast i)))
  refine absurd ?_ ha
  rw [← ha']
  calc ρ (Atom.map (Fin.snoc x y : Fin (k + 1) → Fin n) (Atom.map Fin.castSucc a'))
      = ρ (Atom.map ((Fin.snoc x y : Fin (k + 1) → Fin n) ∘ Fin.castSucc) a') := rfl
    _ = ρ (Atom.map x a') := by rw [Fin.snoc_comp_castSucc]
    _ = D (Atom.map Fin.castSucc a') := congrFun h1 a'

/-- For an injective `x : Fin k → Fin n`, the proportion of structures on `Fin n` in which `x`
has the diagram of `D` on `Fin k` but extends to no tuple with diagram `D` is at most
`(1 - 2 ^ (-c)) ^ (n - k)`, where `c` is the number of new atoms. -/
private theorem ncard_fail_le [L.IsRelational] [Finite L.Symbols] {n k : ℕ} (x : Fin k → Fin n)
    (hx : Function.Injective x) (D : Atom L (Fin (k + 1)) → Prop) :
    ((Set.ncard {S : L.Structure (Fin n) | @diag L (Fin n) S _ x = D ∘ Atom.map Fin.castSucc ∧
        ∀ y, (∀ i, y ≠ x i) → @diag L (Fin n) S _ (Fin.snoc x y : Fin (k + 1) → Fin n) ≠ D} :
          ℕ) : ℝ) ≤
      (1 - 2⁻¹ ^ Nat.card (NewAtom L k)) ^ (n - k) * Nat.card (L.Structure (Fin n)) := by
  have := finite_relSymbols (L := L)
  set J := {y : Fin n // y ∉ Set.range x}
  set G : J × NewAtom L k → Atom L (Fin n) := fun p =>
    Atom.map (Fin.snoc x p.1.1 : Fin (k + 1) → Fin n) p.2.1 with hG
  set Q : (J × NewAtom L k → Prop) → Prop := fun τ => ∀ j, ∃ κ, τ (j, κ) ≠ D κ.1
  have hle : Set.ncard {S : L.Structure (Fin n) |
      @diag L (Fin n) S _ x = D ∘ Atom.map Fin.castSucc ∧
        ∀ y, (∀ i, y ≠ x i) → @diag L (Fin n) S _ (Fin.snoc x y : Fin (k + 1) → Fin n) ≠ D} ≤
      Nat.card {ρ : Atom L (Fin n) → Prop // Q (ρ ∘ G)} := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective
      (fun S => ⟨structureEquiv (Fin n) S.1, fun j => ?_⟩) ?_
    · exact exists_newAtom_ne (ρ := structureEquiv (Fin n) S.1) S.2.1 S.2.2 j.1 j.2
    · intro S S' h
      exact Subtype.ext ((structureEquiv (Fin n)).injective (congrArg Subtype.val h))
  have h1 := card_comp_injective (injective_map_snoc (L := L) hx) Q
  rw [← hG, card_forall_exists_ne (fun (_ : J) (κ : NewAtom L k) => D κ.1), Nat.card_prod] at h1
  have hJ : Nat.card J = n - k := by
    change Nat.card ↥(Set.range x)ᶜ = n - k
    rw [Nat.card_coe_set_eq, Set.ncard_compl, ← Nat.card_coe_set_eq,
      Nat.card_range_of_injective hx]
    simp
  have hStr : Nat.card (L.Structure (Fin n)) = 2 ^ Nat.card (Atom L (Fin n)) := by
    rw [Nat.card_congr (structureEquiv (Fin n)), Nat.card_fun,
      Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop]
  rw [hStr, ← hJ]
  refine (Nat.cast_le.mpr hle).trans (le_of_eq ?_)
  set c := Nat.card (NewAtom L k)
  set m := Nat.card J
  have h1' : (Nat.card {ρ : Atom L (Fin n) → Prop // Q (ρ ∘ G)} : ℝ) * 2 ^ (m * c) =
      ((2 : ℝ) ^ c - 1) ^ m * 2 ^ Nat.card (Atom L (Fin n)) := by
    have h1R := congrArg (Nat.cast : ℕ → ℝ) h1
    push_cast [Nat.one_le_two_pow] at h1R
    exact h1R
  have h2 : ((2 : ℝ) ^ c - 1) ^ m * 2 ^ Nat.card (Atom L (Fin n)) =
      (1 - 2⁻¹ ^ c) ^ m * (2 : ℝ) ^ Nat.card (Atom L (Fin n)) * 2 ^ (m * c) := by
    rw [pow_mul', mul_right_comm, ← mul_pow, sub_mul, one_mul, ← mul_pow, inv_mul_cancel₀
      (two_ne_zero), one_pow]
  rw [h2] at h1'
  push_cast
  exact mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) h1'

/-- An extension axiom fails in a proportion at most `n ^ k * (1 - 2 ^ (-c)) ^ (n - k)` of the
structures on `Fin n`. -/
private theorem satFraction_not_extAxiom_le [L.IsRelational] [Finite L.Symbols] (k : ℕ)
    (D : Atom L (Fin (k + 1)) → Prop) (n : ℕ) :
    L.satFraction (∼(extAxiom k D)) n ≤
      (n : ℝ) ^ k * (1 - 2⁻¹ ^ Nat.card (NewAtom L k)) ^ (n - k) := by
  have := L.finite_structure (Fin n)
  have := L.nonempty_structure (Fin n)
  have hpos : (0 : ℝ) < Nat.card (L.Structure (Fin n)) := by exact_mod_cast Nat.card_pos
  set q : ℝ := 1 - 2⁻¹ ^ Nat.card (NewAtom L k)
  have hq : 0 ≤ q := sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  let F : (Fin k → Fin n) → Set (L.Structure (Fin n)) := fun x =>
    {S | Function.Injective x ∧ @diag L (Fin n) S _ x = D ∘ Atom.map Fin.castSucc ∧
      ∀ y, (∀ i, y ≠ x i) → @diag L (Fin n) S _ (Fin.snoc x y : Fin (k + 1) → Fin n) ≠ D}
  have hsub : {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼(extAxiom k D))} ⊆
      ⋃ x, F x := by
    intro S hS
    replace hS := (@Sentence.realize_not L (Fin n) S _).1 hS
    by_contra hnot
    apply hS
    rw [realize_extAxiom]
    intro x hx h1
    by_contra hno
    exact hnot (Set.mem_iUnion.mpr ⟨x, hx, h1, fun y hy hyD => hno ⟨y, hy, hyD⟩⟩)
  have hF : ∀ x, ((F x).ncard : ℝ) ≤ q ^ (n - k) * Nat.card (L.Structure (Fin n)) := by
    intro x
    by_cases hx : Function.Injective x
    · have hFx : F x = {S : L.Structure (Fin n) |
          @diag L (Fin n) S _ x = D ∘ Atom.map Fin.castSucc ∧
            ∀ y, (∀ i, y ≠ x i) → @diag L (Fin n) S _ (Fin.snoc x y : Fin (k + 1) → Fin n) ≠ D} :=
        Set.ext fun S => and_iff_right hx
      rw [hFx]
      exact ncard_fail_le x hx D
    · have hFx : F x = ∅ := Set.eq_empty_of_forall_notMem fun S hS => hx hS.1
      rw [hFx, Set.ncard_empty, Nat.cast_zero]
      positivity
  unfold satFraction
  rw [div_le_iff₀ hpos]
  calc (({S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼(extAxiom k D))}.ncard : ℕ) :
        ℝ) ≤ ((⋃ x, F x).ncard : ℝ) := Nat.cast_le.mpr (Set.ncard_le_ncard hsub)
    _ ≤ ∑ x, ((F x).ncard : ℝ) := by exact_mod_cast Set.ncard_iUnion_le_of_fintype F
    _ ≤ ∑ _x : Fin k → Fin n, q ^ (n - k) * Nat.card (L.Structure (Fin n)) :=
        Finset.sum_le_sum fun x _ => hF x
    _ = (n : ℝ) ^ k * q ^ (n - k) * Nat.card (L.Structure (Fin n)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        ring

private theorem satFraction_nonneg [L.IsRelational] [Finite L.Symbols] (φ : L.Sentence) (n : ℕ) :
    0 ≤ L.satFraction φ n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem satFraction_le_one [L.IsRelational] [Finite L.Symbols] (φ : L.Sentence) (n : ℕ) :
    L.satFraction φ n ≤ 1 := by
  have h := L.satFraction_not φ n
  have h0 := satFraction_nonneg (∼φ) n
  linarith

/-- Every extension axiom holds almost surely. -/
private theorem tendsto_satFraction_extAxiom [L.IsRelational] [Finite L.Symbols] (k : ℕ)
    (D : Atom L (Fin (k + 1)) → Prop) :
    Tendsto (L.satFraction (extAxiom k D)) atTop (𝓝 1) := by
  set c := Nat.card (NewAtom L k)
  set q : ℝ := 1 - 2⁻¹ ^ c
  set r : ℝ := 1 - 2⁻¹ ^ (c + 1)
  have hq : 0 ≤ q := sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  have hqr : q ≤ r :=
    sub_le_sub_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ c)) 1
  have hr0 : 0 < r := sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero c))
  have hr1 : r < 1 := sub_lt_self 1 (by positivity)
  have hlim : Tendsto (fun n : ℕ => (r ^ k)⁻¹ * ((n : ℝ) ^ k * r ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one k hr0.le hr1).const_mul (r ^ k)⁻¹
  have hbound : ∀ᶠ n : ℕ in atTop,
      1 - (r ^ k)⁻¹ * ((n : ℝ) ^ k * r ^ n) ≤ L.satFraction (extAxiom k D) n := by
    filter_upwards [eventually_ge_atTop k] with n hn
    have h : 1 - L.satFraction (extAxiom k D) n ≤ (n : ℝ) ^ k * q ^ (n - k) := by
      rw [← satFraction_not]
      exact satFraction_not_extAxiom_le k D n
    have hqn : q ^ (n - k) ≤ r ^ (n - k) := pow_le_pow_left₀ hq hqr _
    have hrn : r ^ (n - k) = (r ^ k)⁻¹ * r ^ n := by
      rw [pow_sub₀ r hr0.ne' hn, mul_comm]
    have hnk : (n : ℝ) ^ k * q ^ (n - k) ≤ (r ^ k)⁻¹ * ((n : ℝ) ^ k * r ^ n) := by
      calc (n : ℝ) ^ k * q ^ (n - k) ≤ (n : ℝ) ^ k * r ^ (n - k) :=
            mul_le_mul_of_nonneg_left hqn (by positivity)
        _ = (r ^ k)⁻¹ * ((n : ℝ) ^ k * r ^ n) := by rw [hrn]; ring
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds hbound
    (Eventually.of_forall fun n => satFraction_le_one _ n)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim

/-! ### The theory of extension axioms -/

variable (L) in
/-- The theory of all extension axioms. -/
private noncomputable def extTheory [Finite L.Symbols] : L.Theory :=
  Set.range fun p : Σ k, (Atom L (Fin (k + 1)) → Prop) => extAxiom p.1 p.2

/-- The models of the extension axioms are infinite. -/
private theorem infinite_of_model [Finite L.Symbols] {M : Type w} [L.Structure M] [Nonempty M]
    [h : M ⊨ extTheory L] : Infinite M := by
  have key : ∀ k : ℕ, ∃ x : Fin k → M, Function.Injective x := by
    intro k
    induction k with
    | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ k ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨m⟩ := ‹Nonempty M›
      have hax : M ⊨ extAxiom k (diag (Fin.snoc x m : Fin (k + 1) → M)) :=
        Theory.realize_sentence_of_mem (extTheory L) ⟨⟨k, _⟩, rfl⟩
      obtain ⟨y, hy, -⟩ := (realize_extAxiom k _).1 hax x hx (by
        rw [← diag_comp, Fin.snoc_comp_castSucc])
      refine ⟨Fin.snoc x y, Fin.snoc_injective_of_injective hx ?_⟩
      rintro ⟨i, rfl⟩
      exact hy i rfl
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  obtain ⟨x, hx⟩ := key (Nat.card M + 1)
  have := Nat.card_le_card_of_injective x hx
  simp at this

private theorem mem_closure_singleton_sup_iff [L.IsRelational] {M : Type w} [L.Structure M]
    {S : L.Substructure M} {m u : M} :
    u ∈ (Substructure.closure L {m} ⊔ S) ↔ u = m ∨ u ∈ S := by
  have h : Substructure.closure L {m} ⊔ S = Substructure.closure L (insert m (S : Set M)) := by
    rw [Substructure.closure_insert, Substructure.closure_eq]
  rw [h, Substructure.mem_closure_iff_of_isRelational, Set.mem_insert_iff, SetLike.mem_coe]

/-- The back-and-forth step: a finite partial isomorphism into a model of the extension axioms
extends to any further element of the domain. -/
private theorem isExtensionPair [L.IsRelational] [Finite L.Symbols] {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] [hN : N ⊨ extTheory L] : L.IsExtensionPair M N := by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S hS f m
  by_cases hm : m ∈ S
  · have hle : Substructure.closure L {m} ⊔ S ≤ S :=
      sup_le (Substructure.closure_le.2 (Set.singleton_subset_iff.2 hm)) le_rfl
    exact ⟨f.comp (Substructure.inclusion hle), Embedding.ext fun _ => rfl⟩
  have : Finite S := Substructure.FG.finite hS
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let x : Fin k → M := fun i => (e.symm i : M)
  let y : Fin k → N := fun i => f (e.symm i)
  have hx : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  have hy : Function.Injective y := fun i j h => e.symm.injective (f.injective h)
  have hdiag : diag (L := L) y =
      diag (Fin.snoc x m : Fin (k + 1) → M) ∘ Atom.map Fin.castSucc := by
    rw [← diag_comp, Fin.snoc_comp_castSucc]
    funext a
    exact propext (f.map_rel a.1.2 (e.symm ∘ a.2))
  have hax : N ⊨ extAxiom k (diag (Fin.snoc x m : Fin (k + 1) → M)) :=
    Theory.realize_sentence_of_mem (extTheory L) ⟨⟨k, _⟩, rfl⟩
  obtain ⟨z, hz, hzdiag⟩ := (realize_extAxiom k _).1 hax y hy hdiag
  have hmem : ∀ u : (Substructure.closure L {m} ⊔ S : L.Substructure M), (u : M) ∉ S →
      (u : M) = m := fun u hu => (mem_closure_singleton_sup_iff.1 u.2).resolve_right hu
  let g : (Substructure.closure L {m} ⊔ S : L.Substructure M) → N :=
    fun u => if h : (u : M) ∈ S then f ⟨u, h⟩ else z
  have hfy : ∀ (u : M) (h : u ∈ S), f ⟨u, h⟩ = y (e ⟨u, h⟩) := fun u h => by
    simp only [y, Equiv.symm_apply_apply]
  have hg_inj : Function.Injective g := by
    intro u u' huu'
    by_cases h : (u : M) ∈ S <;> by_cases h' : (u' : M) ∈ S <;>
      simp only [g, h, h', ↓reduceDIte] at huu'
    · exact Subtype.ext (congrArg (fun w : S => (w : M)) (f.injective huu'))
    · exact absurd ((hfy _ h).symm.trans huu') (hz _).symm
    · exact absurd ((hfy _ h').symm.trans huu'.symm) (hz _).symm
    · exact Subtype.ext ((hmem u h).trans (hmem u' h').symm)
  -- the index of an element of `closure {m} ⊔ S` in `Fin.snoc x m`
  let idx : (Substructure.closure L {m} ⊔ S : L.Substructure M) → Fin (k + 1) :=
    fun u => if h : (u : M) ∈ S then (e ⟨u, h⟩).castSucc else Fin.last k
  have hidx_x : ∀ u, (Fin.snoc x m : Fin (k + 1) → M) (idx u) = u := by
    intro u
    by_cases h : (u : M) ∈ S
    · simp only [idx, h, ↓reduceDIte, Fin.snoc_castSucc, x, Equiv.symm_apply_apply]
    · simp only [idx, h, ↓reduceDIte, Fin.snoc_last]
      exact (hmem u h).symm
  have hidx_y : ∀ u, (Fin.snoc y z : Fin (k + 1) → N) (idx u) = g u := by
    intro u
    by_cases h : (u : M) ∈ S
    · simp only [idx, g, h, ↓reduceDIte, Fin.snoc_castSucc]
      exact (hfy _ h).symm
    · simp only [idx, g, h, ↓reduceDIte, Fin.snoc_last]
  refine ⟨{ toFun := g
            inj' := hg_inj
            map_fun' := fun {n} f => isEmptyElim f
            map_rel' := fun {l} r t => ?_ }, ?_⟩
  · have h1 : g ∘ t = (Fin.snoc y z : Fin (k + 1) → N) ∘ (idx ∘ t) :=
      funext fun i => (hidx_y (t i)).symm
    have h2 : (fun i => (t i : M)) = (Fin.snoc x m : Fin (k + 1) → M) ∘ (idx ∘ t) :=
      funext fun i => (hidx_x (t i)).symm
    change RelMap r (g ∘ t) ↔ RelMap r (fun i => (t i : M))
    rw [h1, h2]
    exact Iff.of_eq (congrFun hzdiag ⟨⟨l, r⟩, idx ∘ t⟩)
  · refine Embedding.ext fun u => ?_
    change f u = g _
    simp only [g, Substructure.coe_inclusion, Set.inclusion, u.2, ↓reduceDIte]

/-- The theory of extension axioms is `ℵ₀`-categorical. -/
private theorem categorical [L.IsRelational] [IsEmpty (L.Relations 0)] [Finite L.Symbols] :
    Cardinal.Categorical Cardinal.aleph0.{w} (extTheory L) := by
  intro M N hM hN
  have : Countable M := Cardinal.mk_le_aleph0_iff.1 hM.le
  have : Countable N := Cardinal.mk_le_aleph0_iff.1 hN.le
  obtain ⟨f, -⟩ := equiv_between_cg Structure.cg_of_countable Structure.cg_of_countable
    (default : L.FGEquiv M N) isExtensionPair isExtensionPair
  exact ⟨f⟩

/-- Union bound: if the sentences `ψ i` imply `φ` on `Fin n`, then the proportion of structures
on `Fin n` where `φ` fails is at most the sum of those where the `ψ i` fail. -/
private theorem satFraction_not_le_sum [L.IsRelational] [Finite L.Symbols] (n : ℕ) {ι : Type*}
    [Fintype ι] (ψ : ι → L.Sentence) (φ : L.Sentence)
    (h : ∀ S : L.Structure (Fin n), (∀ i, @Sentence.Realize L (Fin n) S (ψ i)) →
      @Sentence.Realize L (Fin n) S φ) :
    L.satFraction (∼φ) n ≤ ∑ i, L.satFraction (∼(ψ i)) n := by
  have := L.finite_structure (Fin n)
  unfold satFraction
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hsub : {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼φ)} ⊆
      ⋃ i, {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼(ψ i))} := by
    intro S hS
    simp only [Set.mem_ofPred_eq, @Sentence.realize_not L (Fin n) S] at hS
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, @Sentence.realize_not L (Fin n) S]
    by_contra hcon
    exact hS (h S fun i => by_contra fun hi => hcon ⟨i, hi⟩)
  calc ((Set.ncard {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼φ)} : ℕ) : ℝ)
      ≤ ((⋃ i, {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼(ψ i))}).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ i, ((Set.ncard {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S (∼(ψ i))} :
          ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_iUnion_le_of_fintype _

private theorem satFraction_bot [L.IsRelational] [Finite L.Symbols] (n : ℕ) :
    L.satFraction ⊥ n = 0 := by
  have hset : {S : L.Structure (Fin n) | @Sentence.Realize L (Fin n) S ⊥} = ∅ := by
    ext S
    simp [Sentence.Realize, Formula.Realize]
  simp only [satFraction, hset, Set.ncard_empty, Nat.cast_zero, zero_div]

private theorem satFraction_not_eq [L.IsRelational] [Finite L.Symbols] (φ : L.Sentence) :
    L.satFraction (∼φ) = fun n => 1 - L.satFraction φ n :=
  funext (L.satFraction_not φ)

private theorem tendsto_sum_satFraction_not [L.IsRelational] [Finite L.Symbols]
    (T0 : Finset L.Sentence) (hT0 : (T0 : L.Theory) ⊆ extTheory L) :
    Tendsto (fun n => ∑ χ : T0, L.satFraction (∼(χ : L.Sentence)) n) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ _χ : T0, (0 : ℝ) by simp]
  refine tendsto_finsetSum _ fun χ _ => ?_
  obtain ⟨⟨k, D⟩, hkD⟩ := hT0 χ.2
  rw [satFraction_not_eq, ← hkD]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_satFraction_extAxiom k D)

private theorem realize_of_models [L.IsRelational] [Finite L.Symbols] {T0 : Finset L.Sentence}
    {φ : L.Sentence} (h : (T0 : L.Theory) ⊨ᵇ φ) {n : ℕ} (hn : 1 ≤ n) (S : L.Structure (Fin n))
    (hS : ∀ χ : T0, @Sentence.Realize L (Fin n) S χ) : @Sentence.Realize L (Fin n) S φ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let _ := S
  have : Fin n ⊨ (T0 : L.Theory) := (Theory.model_iff _).2 fun χ hχ => hS ⟨χ, hχ⟩
  exact h.realize_sentence (Fin n)

/-- The theory of extension axioms is satisfiable, by compactness: finitely many of them hold
together in some finite structure. -/
private theorem isSatisfiable [L.IsRelational] [Finite L.Symbols] :
    (extTheory L).IsSatisfiable := by
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T0 hT0
  by_contra hns
  have hbound : ∀ n, 1 ≤ n → 1 ≤ ∑ χ : T0, L.satFraction (∼(χ : L.Sentence)) n := by
    intro n hn
    have h1 := satFraction_not_le_sum n (fun χ : T0 => (χ : L.Sentence)) ⊥ (by
      intro S hS
      exfalso
      apply hns
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      let _ := S
      have : Fin n ⊨ (T0 : L.Theory) := (Theory.model_iff _).2 fun χ hχ => hS ⟨χ, hχ⟩
      exact Theory.Model.isSatisfiable (Fin n))
    rwa [satFraction_not, satFraction_bot, sub_zero] at h1
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_sum_satFraction_not T0 hT0).eventually
    (gt_mem_nhds one_pos)).and (eventually_ge_atTop 1)).exists
  linarith [hbound n hn2]

/-- The theory of extension axioms is complete, by the Łoś–Vaught test. -/
private theorem isComplete [L.IsRelational] [IsEmpty (L.Relations 0)] [Finite L.Symbols] :
    (extTheory L).IsComplete := by
  refine (categorical.{u, v, 0}).isComplete _ _ le_rfl ?_ isSatisfiable
    fun M => infinite_of_model (L := L)
  rw [Cardinal.lift_aleph0]
  exact (Cardinal.lift_lt_aleph0.2 (Cardinal.lt_aleph0_of_finite L.Symbols)).le

end Helpers

/-- **Zero-one law for first-order logic.** Let `L` be a relational first-order language with
finitely many symbols and no nullary relation symbol. For every first-order sentence `φ`
(with equality) over `L`, the proportion of `L`-structures on `Fin n` in which `φ` holds
tends to `0` or to `1` as `n → ∞` (Glebskii, Kogan, Liogon'kii and Talanov, Kibernetika 1969;
Fagin, "Probabilities on finite models", J. Symbolic Logic 41, 1976; as stated in Kolaitis
and Vardi, "0-1 laws for fragments of existential second-order logic: a survey", MFCS 2000,
Section 1). -/
theorem zero_one_law (L : Language) [L.IsRelational] [IsEmpty (L.Relations 0)]
    [Finite L.Symbols] (φ : L.Sentence) :
    Tendsto (L.satFraction φ) atTop (𝓝 0) ∨ Tendsto (L.satFraction φ) atTop (𝓝 1) := by
  have key : ∀ ψ : L.Sentence, extTheory L ⊨ᵇ ψ → Tendsto (L.satFraction ψ) atTop (𝓝 1) := by
    intro ψ hψ
    obtain ⟨T0, hT0, hT0ψ⟩ := Theory.models_iff_finset_models.1 hψ
    have hle : ∀ᶠ n in atTop,
        1 - ∑ χ : T0, L.satFraction (∼(χ : L.Sentence)) n ≤ L.satFraction ψ n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have := satFraction_not_le_sum n (fun χ : T0 => (χ : L.Sentence)) ψ
        (realize_of_models hT0ψ hn)
      rw [satFraction_not] at this
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds hle
      (Eventually.of_forall fun n => satFraction_le_one ψ n)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_sum_satFraction_not T0 hT0)
  rcases isComplete.2 φ with h | h
  · exact Or.inr (key φ h)
  · left
    have h1 := key _ h
    rw [satFraction_not_eq] at h1
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

end MathlibExt.ModelTheory.ZeroOneLawWanted
