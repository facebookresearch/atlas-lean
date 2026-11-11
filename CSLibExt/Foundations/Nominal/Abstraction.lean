/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Nominal.Basic
public import Mathlib.Data.Finset.Erase
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Atom abstraction for nominal sets

Atom abstraction `[a]x` (Pitts, *Nominal Sets*, §5) is the quotient of
`Atom × X` by α-equivalence: `(a, x)` and `(b, y)` are equivalent when they
are equal, or when `a ≠ b`, `a` is fresh for `y`, and swapping `a` and `b`
in `x` gives `y`. The abstraction `Abs X` is itself a nominal set, with
support `supp [a]x = (supp x).erase a` and abstraction acting equivariantly.

Main definitions:

* `AbsRel`: the α-equivalence relation on `Atom × X`.
* `Abs X`: the quotient `Atom × X / AbsRel`.
* `abs a x`: the abstraction `[a]x`.

Main results:

* `abs_eq_iff`: `abs a x = abs b y ↔ AbsRel (a, x) (b, y)`.
* `supp_abs`: `supp (abs a x) = (supp x).erase a`.
* `abs_eq_of_same_atom`: `abs a x = abs a y → x = y`.
* `NominalSet Atom (Abs X)`: abstraction is a nominal set.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib
namespace Nominal

variable {Atom : Type*} [Infinite Atom] [DecidableEq Atom]
variable {X : Type*} [MulAction (FinPerm Atom) X] [NominalSet Atom X]

/-- α-equivalence: equal pairs, or a renaming of the bound atom by a fresh
transposition. -/
def AbsRel (a b : Atom) (x y : X) : Prop :=
  (a = b ∧ x = y) ∨
    (a ≠ b ∧ Fresh a y ∧ (swap a b : FinPerm Atom) • x = y)

/-- α-equivalence is reflexive. -/
theorem absRel_refl (a : Atom) (x : X) : AbsRel a a x x := Or.inl ⟨rfl, rfl⟩

/-- α-equivalence is symmetric. Symmetry uses equivariance of support
(`supp_smul`). -/
theorem absRel_symm {a b : Atom} {x y : X} (h : AbsRel a b x y) : AbsRel b a y x := by
  rcases h with ⟨hab, hxy⟩ | ⟨hab, haf, hswap⟩
  · exact Or.inl ⟨hab.symm, hxy.symm⟩
  · refine Or.inr ⟨Ne.symm hab, ?_, ?_⟩
    · -- `b` is fresh for `x`: `b ∈ supp x ↔ a ∈ supp y`.
      have ha_not : a ∉ supp (Atom := Atom) y :=
        (fresh_iff_not_mem_supp (Atom := Atom) y a).mp haf
      have hb : b ∉ supp (Atom := Atom) x := by
        intro hmem
        apply ha_not
        have hmem' : (swap a b : FinPerm Atom) • b ∈
            (supp (Atom := Atom) x).image (swap a b • ·) :=
          Finset.mem_image.mpr ⟨b, hmem, rfl⟩
        rw [← supp_smul, hswap] at hmem'
        rwa [swap_smul, Equiv.swap_apply_right] at hmem'
      exact (fresh_iff_not_mem_supp (Atom := Atom) x b).mpr hb
    · -- `swap b a • y = x`, since `swap b a = swap a b` is an involution.
      rw [swap_comm, ← hswap, ← mul_smul, swap_mul_self, one_smul]

/-- α-equivalence is transitive. Transitivity uses the fact that two
permutations agreeing on `supp y` act equally on `y`
(`smul_eq_of_agree_on_supp`). -/
theorem absRel_trans {a b d : Atom} {x y z : X} (h₁ : AbsRel a b x y)
    (h₂ : AbsRel b d y z) : AbsRel a d x z := by
  rcases h₁ with ⟨hab, hxy⟩ | ⟨hab, haf₁, hswap₁⟩
  · subst hab
    subst hxy
    exact h₂
  · rcases h₂ with ⟨hbd, hyz⟩ | ⟨hbd, hbf₂, hswap₂⟩
    · subst hbd
      subst hyz
      exact Or.inr ⟨hab, haf₁, hswap₁⟩
    · by_cases had : a = d
      · subst had
        -- `x = z`: both are obtained from `y` by the same transposition.
        have hxz : x = z := by
          calc x = (swap a b : FinPerm Atom) • y := by
                rw [← hswap₁, ← mul_smul, swap_mul_self, one_smul]
            _ = (swap b a : FinPerm Atom) • y := by rw [swap_comm]
            _ = z := hswap₂
        exact Or.inl ⟨rfl, hxz⟩
      · refine Or.inr ⟨had, ?_, ?_⟩
        · -- `a` is fresh for `z`: `supp z` is `supp y` permuted by `swap b d`.
          have ha_y : a ∉ supp (Atom := Atom) y :=
            (fresh_iff_not_mem_supp (Atom := Atom) y a).mp haf₁
          have hb_z : b ∉ supp (Atom := Atom) z :=
            (fresh_iff_not_mem_supp (Atom := Atom) z b).mp hbf₂
          have hd_y : d ∉ supp (Atom := Atom) y := by
            intro hdmem
            apply hb_z
            have hmem : (swap b d : FinPerm Atom) • d ∈
                (supp (Atom := Atom) y).image (swap b d • ·) :=
              Finset.mem_image.mpr ⟨d, hdmem, rfl⟩
            rw [← supp_smul, hswap₂] at hmem
            rwa [swap_smul, Equiv.swap_apply_right] at hmem
          have ha_z : a ∉ supp (Atom := Atom) z := by
            intro hamem
            have hz : supp (Atom := Atom) z =
                (supp (Atom := Atom) y).image (swap b d • ·) := by
              rw [← hswap₂, supp_smul]
            rw [hz] at hamem
            obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp hamem
            have hsa : (swap b d : FinPerm Atom) • a = a :=
              swap_smul_of_ne_of_ne hab had
            have hca' : (swap b d : FinPerm Atom) • c =
                (swap b d : FinPerm Atom) • a := by rw [hca, hsa]
            have hc_eq : c = a := MulAction.injective _ hca'
            exact ha_y (hc_eq ▸ hc)
          exact (fresh_iff_not_mem_supp (Atom := Atom) z a).mpr ha_z
        · -- `swap a d • x = z`, via agreement on `supp y`.
          have hx : x = (swap a b : FinPerm Atom) • y := by
            rw [← hswap₁, ← mul_smul, swap_mul_self, one_smul]
          have hagree : ∀ c ∈ supp (Atom := Atom) y,
              ((swap a d : FinPerm Atom) * swap a b) • c =
                (swap b d : FinPerm Atom) • c := by
            intro c hc
            have hca : c ≠ a := by
              intro h
              have ha_y : a ∉ supp (Atom := Atom) y :=
                (fresh_iff_not_mem_supp (Atom := Atom) y a).mp haf₁
              exact ha_y (by rw [← h]; exact hc)
            have hcd : c ≠ d := by
              intro h
              have hd_y : d ∉ supp (Atom := Atom) y := by
                intro hdmem
                have hb_z : b ∉ supp (Atom := Atom) z :=
                  (fresh_iff_not_mem_supp (Atom := Atom) z b).mp hbf₂
                apply hb_z
                have hmem : (swap b d : FinPerm Atom) • d ∈
                    (supp (Atom := Atom) y).image (swap b d • ·) :=
                  Finset.mem_image.mpr ⟨d, hdmem, rfl⟩
                rw [← supp_smul, hswap₂] at hmem
                rwa [swap_smul, Equiv.swap_apply_right] at hmem
              exact hd_y (by rw [← h]; exact hc)
            by_cases hcb : c = b
            · subst hcb
              simp only [mul_smul, swap_smul, Equiv.swap_apply_right,
                Equiv.swap_apply_left]
            · have hcb' : c ≠ b := hcb
              rw [mul_smul]
              have h1 : (swap a b : FinPerm Atom) • c = c :=
                swap_smul_of_ne_of_ne hca hcb'
              rw [h1]
              exact (swap_smul_of_ne_of_ne hca hcd).trans
                (swap_smul_of_ne_of_ne hcb' hcd).symm
          have hmain : ((swap a d : FinPerm Atom) * swap a b) • y =
              (swap b d : FinPerm Atom) • y :=
            smul_eq_of_agree_on_supp hagree
          calc (swap a d : FinPerm Atom) • x
              = ((swap a d : FinPerm Atom) * swap a b) • y := by
                rw [hx, mul_smul]
            _ = (swap b d : FinPerm Atom) • y := hmain
            _ = z := hswap₂


/-- The setoid of α-equivalence. -/
def absSetoid : Setoid (Atom × X) where
  r := fun p q => AbsRel p.1 q.1 p.2 q.2
  iseqv := ⟨fun p => absRel_refl p.1 p.2, fun h => absRel_symm h,
    fun h₁ h₂ => absRel_trans h₁ h₂⟩

/-- Atom abstraction: `[a]x`, the quotient of `Atom × X` by α-equivalence. -/
def Abs (Atom : Type*) [Infinite Atom] [DecidableEq Atom] (X : Type*)
    [MulAction (FinPerm Atom) X] [NominalSet Atom X] : Type _ :=
  Quotient (@absSetoid Atom _ _ X _ _)

/-- The abstraction `[a]x`. -/
def abs (a : Atom) (x : X) : Abs Atom X := Quotient.mk _ (a, x)

/-- Equality of abstractions is α-equivalence. -/
theorem abs_eq_iff {a b : Atom} {x y : X} :
    abs a x = abs b y ↔ AbsRel a b x y :=
  Quotient.eq

/-- An abstraction with the same bound atom determines its body. -/
theorem abs_eq_of_same_atom {a : Atom} {x y : X} (h : abs a x = abs a y) : x = y := by
  rw [abs_eq_iff] at h
  rcases h with ⟨-, hxy⟩ | ⟨hne, -, -⟩
  · exact hxy
  · exact absurd rfl hne

/-- The action of a permutation on abstractions, applied to a representative. -/
def absSmul (π : FinPerm Atom) : Abs Atom X → Abs Atom X :=
  Quotient.lift (fun p : Atom × X => Quotient.mk _ (π • p.1, π • p.2)) (by
    intro p q h
    apply Quotient.sound
    rcases h with ⟨hab, hxy⟩ | ⟨hab, haf, hswap⟩
    · exact Or.inl ⟨congrArg (π • ·) hab, congrArg (π • ·) hxy⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · intro hEq
        exact hab ((MulAction.injective π) hEq)
      · -- `π • a` is fresh for `π • y`.
        have ha_not : p.1 ∉ supp (Atom := Atom) q.2 := by
          -- `p.1 = a`, `q.2 = y`: freshness of `a` for `y`.
          exact (fresh_iff_not_mem_supp (Atom := Atom) q.2 p.1).mp haf
        have hnot : (π • p.1) ∉ supp (Atom := Atom) (π • q.2) := by
          intro hmem
          rw [supp_smul] at hmem
          obtain ⟨c, hc, hEq⟩ := Finset.mem_image.mp hmem
          have hc_eq : c = p.1 := MulAction.injective π hEq
          exact ha_not (hc_eq ▸ hc)
        exact (fresh_iff_not_mem_supp (Atom := Atom) (π • q.2) (π • p.1)).mpr hnot
      · -- `swap (π•a) (π•b) • (π•x) = π•y` by conjugation.
        have hconj : (swap (π • p.1) (π • q.1) : FinPerm Atom) =
            π * swap p.1 q.1 * π⁻¹ := (swap_conj π p.1 q.1).symm
        show (swap (π • p.1) (π • q.1) : FinPerm Atom) • (π • p.2) = π • q.2
        calc (swap (π • p.1) (π • q.1) : FinPerm Atom) • (π • p.2)
            = (π * swap p.1 q.1 * π⁻¹) • (π • p.2) := by rw [hconj]
          _ = π • ((swap p.1 q.1) • (π⁻¹ • (π • p.2))) := by rw [mul_smul, mul_smul]
          _ = π • ((swap p.1 q.1) • p.2) := by
              have h_inv : π⁻¹ • (π • p.2) = p.2 := by
                rw [← mul_smul, inv_mul_cancel, one_smul]
              rw [h_inv]
          _ = π • q.2 := by rw [hswap])

/-- Permutations act on abstractions. -/
instance : MulAction (FinPerm Atom) (Abs Atom X) where
  smul := absSmul
  one_smul := fun u => by
    induction u using Quotient.inductionOn with
    | _ p =>
      show absSmul 1 (Quotient.mk _ p) = Quotient.mk _ p
      obtain ⟨a, x⟩ := p
      show Quotient.mk _ ((1 : FinPerm Atom) • a, (1 : FinPerm Atom) • x) =
        Quotient.mk _ (a, x)
      rw [one_smul, one_smul]
  mul_smul := fun π σ u => by
    induction u using Quotient.inductionOn with
    | _ p =>
      show absSmul (π * σ) (Quotient.mk _ p) = absSmul π (absSmul σ (Quotient.mk _ p))
      obtain ⟨a, x⟩ := p
      show Quotient.mk _ ((π * σ) • a, (π * σ) • x) =
        Quotient.mk _ (π • (σ • a), π • (σ • x))
      rw [mul_smul, mul_smul]

/-- A permutation applied to an abstraction, on representatives. -/
theorem smul_abs (π : FinPerm Atom) (a : Atom) (x : X) :
    π • abs a x = abs (π • a) (π • x) := rfl

/-- The action of a permutation on an abstraction fixes it when the
permutation fixes `supp x \ {a}` pointwise. -/
theorem supports_erase_abs {a : Atom} {x : X} (π : FinPerm Atom)
    (hπ : ∀ c ∈ (supp (Atom := Atom) x).erase a, π • c = c) :
    π • abs a x = abs a x := by
  rw [smul_abs]
  by_cases hπa : π • a = a
  · -- `π` fixes `supp x` pointwise, hence fixes `x`.
    have hfix : π • x = x := by
      apply supp_supports (Atom := Atom) x π
      intro c hc
      by_cases hca : c = a
      · rw [hca]
        exact hπa
      · exact hπ c (Finset.mem_erase.mpr ⟨hca, hc⟩)
    rw [hπa, hfix]
  · -- `(π•a, π•x)` is α-equivalent to `(a, x)`.
    apply Quotient.sound
    refine Or.inr ⟨hπa, ?_, ?_⟩
    · -- `π • a` is fresh for `x`.
      have hnot : (π • a) ∉ supp (Atom := Atom) x := by
        intro hmem
        have hmem' : π • a ∈ (supp (Atom := Atom) x).erase a := by
          apply Finset.mem_erase.mpr
          exact ⟨hπa, hmem⟩
        have hfixed : π • (π • a) = π • a := hπ _ hmem'
        have hinj : π • a = a := MulAction.injective π hfixed
        exact hπa hinj
      exact (fresh_iff_not_mem_supp (Atom := Atom) x (π • a)).mpr hnot
    · -- `swap (π•a) a • (π•x) = x`, since `swap (π•a) a * π` agrees with `1` on `supp x`.
      have hagree : ∀ c ∈ supp (Atom := Atom) x,
          ((swap (π • a) a : FinPerm Atom) * π) • c = (1 : FinPerm Atom) • c := by
        intro c hc
        by_cases hca : c = a
        · subst hca
          rw [mul_smul, swap_smul, Equiv.swap_apply_left, one_smul]
        · have hce : c ∈ (supp (Atom := Atom) x).erase a :=
            Finset.mem_erase.mpr ⟨hca, hc⟩
          have hπc : π • c = c := hπ c hce
          have hcne : c ≠ π • a := by
            intro h
            have hmem : π • a ∈ supp (Atom := Atom) x := by rw [← h]; exact hc
            have hmem' : π • a ∈ (supp (Atom := Atom) x).erase a :=
              Finset.mem_erase.mpr ⟨hπa, hmem⟩
            have hfixed : π • (π • a) = π • a := hπ _ hmem'
            have hinj : π • a = a := MulAction.injective π hfixed
            exact hπa hinj
          rw [mul_smul, hπc, one_smul]
          exact swap_smul_of_ne_of_ne hcne hca
      have hmain : ((swap (π • a) a : FinPerm Atom) * π) • x =
          (1 : FinPerm Atom) • x := smul_eq_of_agree_on_supp hagree
      rw [one_smul] at hmain
      calc (swap (π • a) a : FinPerm Atom) • (π • x)
          = ((swap (π • a) a : FinPerm Atom) * π) • x := by rw [mul_smul]
        _ = x := hmain

/-- The support of `supp x \ {a}` supports `abs a x`, so abstraction is a
nominal set. -/
instance : NominalSet Atom (Abs Atom X) where
  finiteSupport := fun u => by
    induction u using Quotient.inductionOn with
    | _ p =>
      obtain ⟨a, x⟩ := p
      exact ⟨(supp (Atom := Atom) x).erase a, fun π hπ => supports_erase_abs π hπ⟩

/-- The support of an abstraction is the body's support minus the bound atom. -/
theorem supp_abs (a : Atom) (x : X) :
    supp (Atom := Atom) (abs a x) = (supp (Atom := Atom) x).erase a := by
  apply Finset.Subset.antisymm
  · exact supp_subset (Atom := Atom) _ (fun π hπ => supports_erase_abs π hπ)
  · intro c hc
    rw [Finset.mem_erase] at hc
    obtain ⟨hcne, hcx⟩ := hc
    -- From `c ∉ supp (abs a x)`, some support `T` of `abs a x` misses `c`.
    by_contra hcnot
    rw [mem_supp_iff (Atom := Atom)] at hcnot
    push Not at hcnot
    obtain ⟨T, hT, hcT⟩ := hcnot
    obtain ⟨d, -, hd⟩ := Set.infinite_univ.exists_notMem_finset
      (T ∪ supp (Atom := Atom) x ∪ {a, c})
    have hdT : d ∉ T := fun h =>
      hd (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hdS : d ∉ supp (Atom := Atom) x := fun h =>
      hd (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hdc : d ≠ c := fun h => hd (Finset.mem_union_right _
      (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)))
    have hda : d ≠ a := fun h => hd (Finset.mem_union_right _
      (by rw [h]; exact Finset.mem_insert_self a {c}))
    -- `swap c d` fixes `T` pointwise, hence fixes `abs a x`.
    have hfix : (swap c d : FinPerm Atom) • abs a x = abs a x := by
      apply hT
      intro e he
      exact swap_smul_of_ne_of_ne (fun h => hcT (by rw [← h]; exact he))
        (fun h => hdT (by rw [← h]; exact he))
    -- `swap c d` fixes `a`, so `swap c d • x = x` by `abs_eq_of_same_atom`.
    rw [smul_abs, swap_smul_of_ne_of_ne (Ne.symm hcne) (Ne.symm hda)] at hfix
    have hx_eq : (swap c d : FinPerm Atom) • x = x := abs_eq_of_same_atom hfix
    have hd_mem : d ∈ supp (Atom := Atom) x := by
      have hmem : (swap c d : FinPerm Atom) • c ∈
          (supp (Atom := Atom) x).image (swap c d • ·) :=
        Finset.mem_image.mpr ⟨c, hcx, rfl⟩
      rw [← supp_smul, hx_eq] at hmem
      rw [swap_smul, Equiv.swap_apply_left] at hmem
      exact hmem
    exact hdS hd_mem

end Nominal
end Cslib
