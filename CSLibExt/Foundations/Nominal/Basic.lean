/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Sets with atoms (nominal sets)

Sets with atoms, also called *nominal sets* (Pitts, *Nominal Sets: Names and
Symmetry in Computer Science*, Cambridge University Press, 2013), are sets
equipped with an action of the group of finite permutations of a fixed
infinite set of *atoms*, in which every element is fixed by all permutations
that fix some finite set of atoms pointwise. The finite set is the element's
*support*: the atoms it "mentions". Freshness `a # x` means `a` is not in
the support of `x`.

Main definitions:

* `FinPerm Atom`: the group of finitely supported permutations of `Atom`.
* `Supports S x`: `S` supports `x` when every permutation fixing `S`
  pointwise fixes `x`.
* `NominalSet Atom X`: `X` carries an action of `FinPerm Atom` in which every
  element has a finite support.
* `Fresh a x`: `a` is fresh for `x`, witnessed by a support not containing `a`.
* `supp x`: the *least* finite support of `x`, as a `Finset Atom`.

Main results:

* `Supports.inter`: the intersection of two supports is a support.
* `supp_supports`, `supp_subset`: `supp x` is the least finite support.
* `fresh_iff_not_mem_supp`: freshness is exactly non-membership in `supp x`.
* `supp_smul`: support is equivariant, `supp (π • x) = π • supp x`.
* `swap_smul_of_fresh_fresh`: swapping two fresh atoms fixes `x`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib
namespace Nominal

variable {Atom : Type*} [Infinite Atom] [DecidableEq Atom]

/-- The subgroup of finitely supported permutations of `Atom`: permutations
that fix all atoms outside some finite set. -/
def finPermSubgroup (Atom : Type*) [DecidableEq Atom] : Subgroup (Equiv.Perm Atom) where
  carrier := {π | ∃ S : Finset Atom, ∀ a, a ∉ S → π a = a}
  one_mem' := ⟨∅, fun _ _ => rfl⟩
  mul_mem' := by
    intro π σ hπ hσ
    obtain ⟨Sπ, hSπ⟩ := hπ
    obtain ⟨Sσ, hSσ⟩ := hσ
    refine ⟨Sπ ∪ Sσ, fun a ha => ?_⟩
    have haπ : a ∉ Sπ := fun h => ha (Finset.mem_union_left Sσ h)
    have haσ : a ∉ Sσ := fun h => ha (Finset.mem_union_right Sπ h)
    rw [Equiv.Perm.mul_apply, hSσ a haσ, hSπ a haπ]
  inv_mem' := by
    intro π hπ
    obtain ⟨S, hS⟩ := hπ
    refine ⟨S, fun a ha => ?_⟩
    have h : π a = a := hS a ha
    have h' : π⁻¹ (π a) = π⁻¹ a := congrArg (⇑π⁻¹) h
    rw [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h'
    exact h'.symm

/-- The group of finitely supported permutations of `Atom`. -/
abbrev FinPerm (Atom : Type*) [DecidableEq Atom] : Type _ := ↥(finPermSubgroup Atom)

/-- A finite permutation acts on atoms by applying the underlying permutation. -/
instance : MulAction (FinPerm Atom) Atom where
  smul := fun π a => π.1 a
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

/-- The transposition of two atoms, as a finite permutation. -/
def swap (a b : Atom) : FinPerm Atom :=
  ⟨Equiv.swap a b, ⟨{a, b}, fun x hx => by
    by_contra h
    exact h (Equiv.swap_apply_of_ne_of_ne
      (fun h₁ => hx (Finset.mem_insert.mpr (Or.inl h₁)))
      (fun h₂ => hx (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h₂)))))⟩⟩

/-- Applying a transposition is applying the underlying `Equiv.swap`. -/
theorem swap_smul (a b c : Atom) :
    (swap a b : FinPerm Atom) • c = Equiv.swap a b c := rfl

/-- A transposition is an involution, stated for the `FinPerm` group. -/
theorem swap_mul_self (a b : Atom) : (swap a b : FinPerm Atom) * swap a b = 1 := by
  rw [Subtype.ext_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_one]
  exact Equiv.swap_mul_self a b

/-- A transposition is its own inverse. -/
theorem swap_inv (a b : Atom) : (swap a b : FinPerm Atom)⁻¹ = swap a b := by
  exact (eq_inv_of_mul_eq_one_left (swap_mul_self a b)).symm

/-- A transposition of an atom with itself is the identity. -/
theorem swap_self (a : Atom) : (swap a a : FinPerm Atom) = 1 := by
  rw [Subtype.ext_iff]
  simp only [Subgroup.coe_one]
  exact Equiv.swap_self a

/-- Transpositions are symmetric. -/
theorem swap_comm (a b : Atom) : (swap a b : FinPerm Atom) = swap b a := by
  rw [Subtype.ext_iff]
  exact Equiv.swap_comm a b

/-- Conjugation of a transposition: `σ * swap b c * σ⁻¹ = swap (σ b) (σ c)`. -/
theorem swap_conj (σ : FinPerm Atom) (b c : Atom) :
    σ * swap b c * σ⁻¹ = swap (σ • b) (σ • c) := by
  rw [Subtype.ext_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Equiv.swap_apply_apply σ.1 b c).symm

/-- A transposition fixes every atom distinct from its two swapped atoms. -/
theorem swap_smul_of_ne_of_ne {a b c : Atom} (h1 : c ≠ a) (h2 : c ≠ b) :
    (swap a b : FinPerm Atom) • c = c := by
  rw [swap_smul]
  exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- `S` supports `x` when every finite permutation fixing `S` pointwise fixes `x`. -/
def Supports {X : Type*} [MulAction (FinPerm Atom) X] (S : Finset Atom) (x : X) : Prop :=
  ∀ π : FinPerm Atom, (∀ a ∈ S, π • a = a) → π • x = x

/-- A support can be enlarged: fixing a larger set pointwise is a stronger
hypothesis. -/
theorem Supports.mono {X : Type*} [MulAction (FinPerm Atom) X] {S T : Finset Atom}
    {x : X} (h : S ⊆ T) (hs : Supports S x) : Supports T x :=
  fun π hπ => hs π (fun a ha => hπ a (h ha))

/-- A type with an action of finite permutations in which every element has a
finite support: a *nominal set*. -/
class NominalSet (Atom : Type*) [DecidableEq Atom] (X : Type*) [MulAction (FinPerm Atom) X] : Prop where
  finiteSupport : ∀ x : X, ∃ S : Finset Atom, Supports S x

/-- Atoms form a nominal set over themselves, supported by the singleton. -/
instance instNominalAtom : NominalSet Atom Atom where
  finiteSupport := fun a => ⟨{a}, fun π h => h a (Finset.mem_singleton_self a)⟩

instance instMulActionProd {X Y : Type*} [MulAction (FinPerm Atom) X]
    [MulAction (FinPerm Atom) Y] : MulAction (FinPerm Atom) (X × Y) where
  smul := fun π p => (π • p.1, π • p.2)
  one_smul := fun p => Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul := fun π σ p => Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)

/-- A product of nominal sets is a nominal set, supported by the union of
the supports. -/
instance instNominalProd {X Y : Type*} [MulAction (FinPerm Atom) X]
    [MulAction (FinPerm Atom) Y] [NominalSet Atom X] [NominalSet Atom Y] :
    NominalSet Atom (X × Y) where
  finiteSupport := fun ⟨x, y⟩ => by
    obtain ⟨Sx, hSx⟩ := show ∃ S : Finset Atom, Supports S x from NominalSet.finiteSupport x
    obtain ⟨Sy, hSy⟩ := NominalSet.finiteSupport (Atom := Atom) (X := Y) y
    refine ⟨Sx ∪ Sy, fun π hπ => ?_⟩
    have hx : π • x = x := hSx π (fun a ha => hπ a (Finset.mem_union_left Sy ha))
    have hy : π • y = y := hSy π (fun a ha => hπ a (Finset.mem_union_right Sx ha))
    exact Prod.ext hx hy

/-- A pair is supported by the union of supports of its components. -/
theorem Supports.prod {X Y : Type*} [MulAction (FinPerm Atom) X]
    [MulAction (FinPerm Atom) Y] {S T : Finset Atom} {x : X} {y : Y}
    (hx : Supports S x) (hy : Supports T y) : Supports (S ∪ T) (x, y) := by
  intro π hπ
  exact Prod.ext (hx π (fun a ha => hπ a (Finset.mem_union_left T ha)))
    (hy π (fun a ha => hπ a (Finset.mem_union_right S ha)))

/-- `a` is *fresh* for `x`, written `a # x` in the nominal literature, when
some finite support of `x` does not contain `a`. -/
def Fresh {X : Type*} [MulAction (FinPerm Atom) X] (a : Atom) (x : X) : Prop :=
  ∃ S : Finset Atom, Supports S x ∧ a ∉ S

/-- Every element has a fresh atom: choose one outside any of its supports. -/
theorem exists_fresh {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]
    (x : X) : ∃ a : Atom, Fresh a x := by
  obtain ⟨S, hS⟩ := show ∃ S : Finset Atom, Supports S x from NominalSet.finiteSupport x
  obtain ⟨a, -, ha⟩ := Set.infinite_univ.exists_notMem_finset S
  exact ⟨a, S, hS, ha⟩

/-- A transposition of two atoms both outside a support of `x` fixes `x`. -/
theorem swap_smul_of_supports_not_mem {X : Type*} [MulAction (FinPerm Atom) X]
    {S : Finset Atom} {x : X} (hS : Supports S x) {a b : Atom} (ha : a ∉ S)
    (hb : b ∉ S) : (swap a b : FinPerm Atom) • x = x := by
  apply hS
  intro d hd
  apply swap_smul_of_ne_of_ne
  · exact fun h => ha (by rw [← h]; exact hd)
  · exact fun h => hb (by rw [← h]; exact hd)

/-- Swapping two fresh atoms fixes `x`. The proof uses a third atom `c` fresh
for both witnessing supports, and the conjugation identity
`swap a b = swap a c * swap b c * swap a c`. -/
theorem swap_smul_of_fresh_fresh {X : Type*} [MulAction (FinPerm Atom) X]
    {x : X} {a b : Atom} (ha : Fresh a x) (hb : Fresh b x) :
    (swap a b : FinPerm Atom) • x = x := by
  by_cases hab : a = b
  · subst hab
    rw [swap_self]
    exact one_smul _ _
  · obtain ⟨Sa, hSa, haSa⟩ := ha
    obtain ⟨Sb, hSb, hbSb⟩ := hb
    obtain ⟨c, -, hc⟩ := Set.infinite_univ.exists_notMem_finset (Sa ∪ Sb ∪ {a, b})
    have hcSa : c ∉ Sa := fun h => hc (Finset.mem_union_left {a, b} (Finset.mem_union_left Sb h))
    have hcSb : c ∉ Sb := fun h => hc (Finset.mem_union_left {a, b} (Finset.mem_union_right Sa h))
    have hcb : c ≠ b := fun h => hc (Finset.mem_union_right _
      (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
    have hac : (swap a c : FinPerm Atom) • x = x :=
      swap_smul_of_supports_not_mem hSa haSa hcSa
    have hbc : (swap b c : FinPerm Atom) • x = x :=
      swap_smul_of_supports_not_mem hSb hbSb hcSb
    have hconj : (swap a b : FinPerm Atom) =
        swap a c * swap b c * swap a c := by
      have h := swap_conj (σ := (swap a c : FinPerm Atom)) b c
      rw [swap_inv] at h
      have hb' : (swap a c : FinPerm Atom) • b = b := by
        rw [swap_smul]
        exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)
      have hc' : (swap a c : FinPerm Atom) • c = a := by
        rw [swap_smul]
        exact Equiv.swap_apply_right a c
      calc (swap a b : FinPerm Atom) = swap b a := swap_comm a b
        _ = swap ((swap a c : FinPerm Atom) • b) ((swap a c : FinPerm Atom) • c) := by
            rw [hb', hc']
        _ = swap a c * swap b c * swap a c := h.symm
    rw [hconj, mul_smul, mul_smul, hac, hbc, hac]

/-- A permutation that fixes every atom outside a finite set `F` of fresh
atoms fixes `x`, by induction on `F`. If `π a = a` we apply the induction
hypothesis to `π`; otherwise we factor `π = swap a b * π'` with `b = π a`,
where `π'` fixes `a` and has support inside `F \ {a}`, and `swap a b` fixes
`x` since `a` and `b` are fresh. -/
theorem smul_eq_of_fresh {X : Type*} [MulAction (FinPerm Atom) X] {x : X}
    (F : Finset Atom) (hF : ∀ a ∈ F, Fresh a x) :
    ∀ π : FinPerm Atom, (∀ a ∉ F, π • a = a) → π • x = x := by
  induction F using Finset.induction with
  | empty =>
    intro π hπ
    have hπ1 : π = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro a
      exact hπ a (Finset.notMem_empty a)
    rw [hπ1]
    exact one_smul _ _
  | insert a F' ha ih =>
    intro π hπ
    by_cases hba : π • a = a
    · apply ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      intro b hb
      by_cases hbca : b = a
      · rw [hbca]
        exact hba
      · exact hπ b (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hbca, hb⟩)
    · set b := π • a with hbdef
      have hbF : b ∈ insert a F' := by
        by_contra hbnot
        have hπb : π • b = b := hπ b hbnot
        have h1 : a = π⁻¹ • b := by
          rw [hbdef, ← mul_smul, inv_mul_cancel, one_smul]
        have h2 : π⁻¹ • b = b := by
          calc π⁻¹ • b = π⁻¹ • (π • b) := by rw [hπb]
            _ = b := by rw [← mul_smul, inv_mul_cancel, one_smul]
        exact (Ne.symm hba) (h1.trans h2)
      have hbFresh : Fresh b x := hF b hbF
      have haFresh : Fresh a x := hF a (Finset.mem_insert_self a F')
      set π' : FinPerm Atom := swap a b * π with hπ'def
      have hπ'x : π' • x = x := by
        apply ih (fun c hc => hF c (Finset.mem_insert_of_mem hc))
        intro c hc
        by_cases hca : c = a
        · subst hca
          rw [hπ'def, mul_smul, ← hbdef, swap_smul, Equiv.swap_apply_right]
        · have hcF : c ∉ insert a F' := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨hca, hc⟩
          have hcne_b : c ≠ b := fun h => hcF (by rw [h]; exact hbF)
          have hπc : π • c = c := hπ c hcF
          rw [hπ'def, mul_smul, hπc]
          exact swap_smul_of_ne_of_ne hca hcne_b
      have hπeq : π = swap a b * π' := by
        rw [hπ'def, ← mul_assoc, swap_mul_self, one_mul]
      calc π • x = (swap a b * π') • x := by rw [hπeq]
        _ = (swap a b) • (π' • x) := by rw [mul_smul]
        _ = (swap a b) • x := by rw [hπ'x]
        _ = x := swap_smul_of_fresh_fresh haFresh hbFresh

/-- The intersection of two supports is a support: a permutation fixing the
intersection fixes `x`, since every atom it can move (outside some finite
support of the permutation, and outside the intersection) is fresh for `x`. -/
theorem Supports.inter {X : Type*} [MulAction (FinPerm Atom) X]
    {S₁ S₂ : Finset Atom} {x : X} (h₁ : Supports S₁ x) (h₂ : Supports S₂ x) :
    Supports (S₁ ∩ S₂) x := by
  refine fun π hπ => ?_
  have hπmem : ∃ S : Finset Atom, ∀ a, a ∉ S → π.1 a = a := π.2
  obtain ⟨Sπ, hSπ⟩ := hπmem
  refine smul_eq_of_fresh (Sπ \ (S₁ ∩ S₂)) ?_ π ?_
  · intro a ha
    have haInt : a ∉ S₁ ∩ S₂ := (Finset.mem_sdiff.mp ha).2
    by_cases haS₁ : a ∈ S₁
    · exact ⟨S₂, h₂, fun h => haInt (Finset.mem_inter.mpr ⟨haS₁, h⟩)⟩
    · exact ⟨S₁, h₁, haS₁⟩
  · intro a ha
    by_cases haInt : a ∈ S₁ ∩ S₂
    · exact hπ a haInt
    · have haSπ : a ∉ Sπ := by
        by_contra h
        exact ha (Finset.mem_sdiff.mpr ⟨h, haInt⟩)
      exact hSπ a haSπ

/-- A permutation moves a support of `x` to a support of `π • x`. -/
theorem Supports.image {X : Type*} [MulAction (FinPerm Atom) X] {S : Finset Atom}
    {x : X} (hS : Supports S x) (π : FinPerm Atom) :
    Supports (S.image (π • ·)) (π • x) := by
  intro σ hσ
  have hτ : (π⁻¹ * σ * π) • x = x := by
    apply hS
    intro a ha
    show (π⁻¹ * σ * π) • a = a
    rw [mul_smul, mul_smul]
    have hσa : σ • (π • a) = π • a := by
      apply hσ
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [hσa]
    show π⁻¹ • (π • a) = a
    rw [← mul_smul, inv_mul_cancel, one_smul]
  calc σ • (π • x) = π • ((π⁻¹ * σ * π) • x) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        simp [mul_assoc]
    _ = π • x := by rw [hτ]

/-- A least finite support exists: among the supports of `x`, one is
contained in every support. The proof is by strong induction on a chosen
support `S₀`: either every element of `S₀` lies in every support (so `S₀`
itself is least), or some `a ∈ S₀` is missing from a support `Sₐ`, and the
induction hypothesis applies to the strictly smaller support `Sₐ ∩ S₀`. -/
theorem exists_least_support {X : Type*} [MulAction (FinPerm Atom) X] (x : X)
    (S₀ : Finset Atom) (hS₀ : Supports S₀ x) :
    ∃ S : Finset Atom, Supports S x ∧ S ⊆ S₀ ∧
      ∀ T : Finset Atom, Supports T x → S ⊆ T := by
  induction S₀ using Finset.strongInduction with
  | _ S₀ IH =>
    by_cases h : ∀ a ∈ S₀, ∀ S : Finset Atom, Supports S x → a ∈ S
    · exact ⟨S₀, hS₀, Finset.Subset.refl S₀, fun T hT a ha => h a ha T hT⟩
    · push Not at h
      obtain ⟨a, haS₀, Sₐ, hSₐ, haSₐ⟩ := h
      set S₁ := Sₐ ∩ S₀ with hS₁def
      have hS₁ : Supports S₁ x := hSₐ.inter hS₀
      have hsub : S₁ ⊂ S₀ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
        intro hEq
        have haS₁ : a ∈ S₁ := hEq.symm ▸ haS₀
        exact haSₐ (Finset.mem_inter.mp haS₁).1
      obtain ⟨S, hS, hSS₁, hmin⟩ := IH S₁ hsub hS₁
      exact ⟨S, hS, hSS₁.trans Finset.inter_subset_right, hmin⟩

/-- The *least* finite support of `x`: a support contained in every support
of `x`. -/
noncomputable def supp {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]
    (x : X) : Finset Atom :=
  Classical.choose (exists_least_support x _
    (Classical.choose_spec (show ∃ S : Finset Atom, Supports S x from NominalSet.finiteSupport x)))

/-- The least support is a support. -/
theorem supp_supports {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]
    (x : X) : Supports (supp (Atom := Atom) x) x :=
  (Classical.choose_spec (exists_least_support x _
    (Classical.choose_spec (show ∃ S : Finset Atom, Supports S x from NominalSet.finiteSupport x)))).1

/-- The least support is contained in every support: minimality. -/
theorem supp_subset {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]
    (x : X) {S : Finset Atom} (hS : Supports S x) : supp (Atom := Atom) x ⊆ S :=
  (Classical.choose_spec (exists_least_support x _
    (Classical.choose_spec (show ∃ S : Finset Atom, Supports S x from NominalSet.finiteSupport x)))).2.2 S hS

/-- Membership in the least support: `a ∈ supp (Atom := Atom) x` iff `a` lies in every
support of `x`. -/
theorem mem_supp_iff {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]
    (x : X) (a : Atom) : a ∈ supp (Atom := Atom) x ↔ ∀ S : Finset Atom, Supports S x → a ∈ S := by
  constructor
  · intro h S hS
    exact supp_subset (Atom := Atom) x hS h
  · intro h
    exact h _ (supp_supports (Atom := Atom) x)

/-- Freshness is exactly non-membership in the least support. -/
theorem fresh_iff_not_mem_supp {X : Type*} [MulAction (FinPerm Atom) X]
    [NominalSet Atom X] (x : X) (a : Atom) : Fresh a x ↔ a ∉ supp (Atom := Atom) x := by
  constructor
  · rintro ⟨S, hS, haS⟩ hmem
    exact haS (supp_subset (Atom := Atom) x hS hmem)
  · intro hnot
    by_contra hFresh
    apply hnot
    rw [mem_supp_iff]
    intro S hS
    by_contra hna
    exact hFresh ⟨S, hS, hna⟩

/-- Support is equivariant: permuting `x` permutes its support. -/
theorem supp_smul {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]
    (x : X) (π : FinPerm Atom) :
    supp (Atom := Atom) (π • x) = (supp (Atom := Atom) x).image (π • ·) := by
  apply Finset.Subset.antisymm
  · exact supp_subset _ ((supp_supports (Atom := Atom) x).image π)
  · have hsupp : Supports ((supp (Atom := Atom) (π • x)).image (π⁻¹ • ·)) x := by
      have h := (supp_supports (Atom := Atom) (π • x)).image π⁻¹
      rwa [← mul_smul, inv_mul_cancel, one_smul] at h
    have h : supp (Atom := Atom) x ⊆ (supp (Atom := Atom) (π • x)).image (π⁻¹ • ·) :=
      supp_subset _ hsupp
    refine Finset.Subset.trans (Finset.image_subset_image h) ?_
    intro a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨b, hb, hba⟩ := ha
    obtain ⟨c, hc, hcb⟩ := hb
    rw [← hba, ← hcb]
    have hbc : π • (π⁻¹ • c) = c := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [hbc]
    exact hc

/-- The support of an atom is its singleton. -/
theorem supp_atom (a : Atom) : supp (Atom := Atom) (a : Atom) = {a} := by
  apply Finset.Subset.antisymm
  · exact supp_subset _ (fun π h => h a (Finset.mem_singleton_self a))
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    rw [hb]
    rw [mem_supp_iff]
    intro S hS
    by_contra hna
    obtain ⟨c, -, hc⟩ := Set.infinite_univ.exists_notMem_finset (S ∪ {a})
    have hcS : c ∉ S := fun h => hc (Finset.mem_union_left {a} h)
    have hca : c ≠ a := fun h => hc (Finset.mem_union_right S (Finset.mem_singleton.mpr h))
    have hswap : (swap a c : FinPerm Atom) • (a : Atom) = a := by
      apply hS
      intro d hd
      apply swap_smul_of_ne_of_ne
      · exact fun h => hna (by rw [← h]; exact hd)
      · exact fun h => hcS (by rw [← h]; exact hd)
    rw [swap_smul, Equiv.swap_apply_left] at hswap
    exact hca hswap

/-- Two permutations that agree on the support of `x` act equally on `x`:
their ratio fixes the support pointwise, hence fixes `x`. -/
theorem smul_eq_of_agree_on_supp {X : Type*} [MulAction (FinPerm Atom) X]
    [NominalSet Atom X] {x : X} {π σ : FinPerm Atom}
    (h : ∀ a ∈ supp (Atom := Atom) x, π • a = σ • a) : π • x = σ • x := by
  have hτ : (σ⁻¹ * π) • x = x := by
    apply supp_supports (Atom := Atom) x
    intro a ha
    rw [mul_smul, h a ha, ← mul_smul, inv_mul_cancel, one_smul]
  calc π • x = σ • ((σ⁻¹ * π) • x) := by
        rw [← mul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = σ • x := by rw [hτ]

/-- An element fixed by every permutation has the empty set as a support. -/
def IsEquivariant {X : Type*} [MulAction (FinPerm Atom) X] (x : X) : Prop :=
  ∀ π : FinPerm Atom, π • x = x

/-- An equivariant element is supported by the empty set. -/
theorem supports_empty_of_equivariant {X : Type*} [MulAction (FinPerm Atom) X]
    {x : X} (h : IsEquivariant (Atom := Atom) x) : Supports (∅ : Finset Atom) x := by
  intro π _
  exact h π

/-- An equivariant element has empty support. -/
theorem supp_eq_empty_of_equivariant {X : Type*} [MulAction (FinPerm Atom) X]
    [NominalSet Atom X] {x : X} (h : IsEquivariant (Atom := Atom) x) : supp (Atom := Atom) x = (∅ : Finset Atom) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a ha
  exact (Finset.notMem_empty a) (supp_subset (Atom := Atom) x (show Supports (∅ : Finset Atom) x from supports_empty_of_equivariant h) ha)

end Nominal
end Cslib
