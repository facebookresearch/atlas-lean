/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22QuadraticDetection
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Every binary quadratic on eleven coordinates has the checked sixty-six monomial coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The canonical coordinate vector for the eleven-dimensional auxiliary binary space. -/
def co1ResidueM22QuadraticUnit (i : Fin 11) : Fin 11 → ZMod 2 := Pi.single i 1

/-- The square or polar coefficient at each of the sixty-six checked monomial addresses. -/
def co1ResidueM22QuadraticCoefficients
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) (k : Fin 66) : ZMod 2 :=
  let ab := co1ResidueM22QuadraticTerms k
  if ab.1 = ab.2 then Q (co1ResidueM22QuadraticUnit ab.1)
  else QuadraticMap.polar Q (co1ResidueM22QuadraticUnit ab.1)
    (co1ResidueM22QuadraticUnit ab.2)

/-- The polynomial assembled from the original square and polar coefficients. -/
def co1ResidueM22QuadraticExpansion
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) :
    QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2) :=
  ∑ k : Fin 66, co1ResidueM22QuadraticCoefficients Q k •
    QuadraticMap.linMulLin (LinearMap.proj (co1ResidueM22QuadraticTerms k).1)
      (LinearMap.proj (co1ResidueM22QuadraticTerms k).2)

/-- The assembled quadratic map evaluates to the exact monomial polynomial. -/
theorem co1ResidueM22QuadraticExpansion_apply
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) (x : Fin 11 → ZMod 2) :
    co1ResidueM22QuadraticExpansion Q x =
      co1ResidueM22QuadraticPolynomial (co1ResidueM22QuadraticCoefficients Q) x := by
  simp only [co1ResidueM22QuadraticExpansion, sum_apply,
    smul_apply, QuadraticMap.linMulLin_apply, LinearMap.proj_apply,
    co1ResidueM22QuadraticPolynomial, smul_eq_mul]
  congr 1
  funext k
  ring

private theorem terms_injective : Function.Injective co1ResidueM22QuadraticTerms := by
  decide +kernel

private theorem terms_diagonal (i : Fin 11) :
    co1ResidueM22QuadraticTerms (⟨i.val, by omega⟩ : Fin 66) = (i, i) := by
  have h : ∀ i : Fin 11,
      co1ResidueM22QuadraticTerms (⟨i.val, by omega⟩ : Fin 66) = (i, i) := by
    decide +kernel
  exact h i

private theorem terms_upper (k : Fin 66) :
    (co1ResidueM22QuadraticTerms k).1 ≤ (co1ResidueM22QuadraticTerms k).2 := by
  have h : ∀ k : Fin 66,
      (co1ResidueM22QuadraticTerms k).1 ≤ (co1ResidueM22QuadraticTerms k).2 := by
    decide +kernel
  exact h k

private theorem terms_cover (i j : Fin 11) (hij : i ≤ j) :
    ∃ k : Fin 66, co1ResidueM22QuadraticTerms k = (i, j) := by
  have h : ∀ i j : Fin 11, i ≤ j →
      ∃ k : Fin 66, co1ResidueM22QuadraticTerms k = (i, j) := by
    decide +kernel
  exact h i j hij

private theorem polynomial_unit (c : Fin 66 → ZMod 2) (i : Fin 11) :
    co1ResidueM22QuadraticPolynomial c (co1ResidueM22QuadraticUnit i) =
      c (⟨i.val, by omega⟩ : Fin 66) := by
  let d : Fin 66 := ⟨i.val, by omega⟩
  have hd : co1ResidueM22QuadraticTerms d = (i, i) := terms_diagonal i
  rw [co1ResidueM22QuadraticPolynomial, Finset.sum_eq_single d]
  · simp only [hd, co1ResidueM22QuadraticUnit, Pi.single_eq_same, one_mul, one_smul]
    rfl
  · intro k _ hkd
    have hn : ¬ ((co1ResidueM22QuadraticTerms k).1 = i ∧
        (co1ResidueM22QuadraticTerms k).2 = i) := by
      intro hab
      exact hkd (terms_injective ((Prod.ext hab.1 hab.2).trans hd.symm))
    rcases not_and_or.mp hn with ha | hb
    · simp [co1ResidueM22QuadraticUnit, Pi.single_apply, ha]
    · simp [co1ResidueM22QuadraticUnit, Pi.single_apply, hb]
  · simp

private theorem expansion_unit
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) (i : Fin 11) :
    co1ResidueM22QuadraticExpansion Q (co1ResidueM22QuadraticUnit i) =
      Q (co1ResidueM22QuadraticUnit i) := by
  rw [co1ResidueM22QuadraticExpansion_apply, polynomial_unit]
  simp only [co1ResidueM22QuadraticCoefficients, terms_diagonal, ite_true]

private theorem expansion_polar
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2))
    (x y : Fin 11 → ZMod 2) :
    QuadraticMap.polar (co1ResidueM22QuadraticExpansion Q) x y =
      ∑ k : Fin 66,
        (x (co1ResidueM22QuadraticTerms k).1 * y (co1ResidueM22QuadraticTerms k).2 +
          y (co1ResidueM22QuadraticTerms k).1 * x (co1ResidueM22QuadraticTerms k).2) *
            co1ResidueM22QuadraticCoefficients Q k := by
  simp only [QuadraticMap.polar, co1ResidueM22QuadraticExpansion_apply,
    co1ResidueM22QuadraticPolynomial, Pi.add_apply, smul_eq_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem expansion_polar_lt
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) (i j : Fin 11) (hij : i < j) :
    QuadraticMap.polar (co1ResidueM22QuadraticExpansion Q)
        (co1ResidueM22QuadraticUnit i) (co1ResidueM22QuadraticUnit j) =
      QuadraticMap.polar Q (co1ResidueM22QuadraticUnit i) (co1ResidueM22QuadraticUnit j) := by
  obtain ⟨d, hd⟩ := terms_cover i j hij.le
  rw [expansion_polar, Finset.sum_eq_single d]
  · simp [hd, co1ResidueM22QuadraticCoefficients, co1ResidueM22QuadraticUnit,
      hij.ne, hij.ne.symm]
  · intro k _ hkd
    have hf : ¬ ((co1ResidueM22QuadraticTerms k).1 = i ∧
        (co1ResidueM22QuadraticTerms k).2 = j) := by
      intro hab
      exact hkd (terms_injective ((Prod.ext hab.1 hab.2).trans hd.symm))
    have hr : ¬ ((co1ResidueM22QuadraticTerms k).1 = j ∧
        (co1ResidueM22QuadraticTerms k).2 = i) := by
      intro hab
      have hle := terms_upper k
      rw [hab.1, hab.2] at hle
      exact (not_le_of_gt hij) hle
    have hf0 : co1ResidueM22QuadraticUnit i (co1ResidueM22QuadraticTerms k).1 *
        co1ResidueM22QuadraticUnit j (co1ResidueM22QuadraticTerms k).2 = 0 := by
      rcases not_and_or.mp hf with ha | hb
      · simp [co1ResidueM22QuadraticUnit, Pi.single_apply, ha]
      · simp [co1ResidueM22QuadraticUnit, Pi.single_apply, hb]
    have hr0 : co1ResidueM22QuadraticUnit j (co1ResidueM22QuadraticTerms k).1 *
        co1ResidueM22QuadraticUnit i (co1ResidueM22QuadraticTerms k).2 = 0 := by
      rcases not_and_or.mp hr with ha | hb
      · simp [co1ResidueM22QuadraticUnit, Pi.single_apply, ha]
      · simp [co1ResidueM22QuadraticUnit, Pi.single_apply, hb]
    rw [hf0, hr0, zero_add, zero_mul]
  · simp

private theorem expansion_polar_unit
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) (i j : Fin 11) :
    QuadraticMap.polar (co1ResidueM22QuadraticExpansion Q)
        (co1ResidueM22QuadraticUnit i) (co1ResidueM22QuadraticUnit j) =
      QuadraticMap.polar Q (co1ResidueM22QuadraticUnit i) (co1ResidueM22QuadraticUnit j) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact expansion_polar_lt Q i j hij
  · rw [QuadraticMap.polar_self, QuadraticMap.polar_self, expansion_unit]
  · rw [QuadraticMap.polar_comm _ (co1ResidueM22QuadraticUnit i),
      QuadraticMap.polar_comm Q (co1ResidueM22QuadraticUnit i)]
    exact expansion_polar_lt Q j i hji

/-- Every genuine quadratic map equals its square-and-polar coefficient polynomial. -/
theorem co1ResidueM22QuadraticExpansion_eq
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2)) :
    co1ResidueM22QuadraticExpansion Q = Q := by
  have hB : (co1ResidueM22QuadraticExpansion Q).polarBilin = Q.polarBilin := by
    apply (Pi.basisFun (ZMod 2) (Fin 11)).ext
    intro i
    apply (Pi.basisFun (ZMod 2) (Fin 11)).ext
    intro j
    simpa only [QuadraticMap.polarBilin_apply_apply, Pi.basisFun_apply,
      co1ResidueM22QuadraticUnit] using expansion_polar_unit Q i j
  have hp (x y : Fin 11 → ZMod 2) :
      QuadraticMap.polar (co1ResidueM22QuadraticExpansion Q) x y =
        QuadraticMap.polar Q x y := congrArg (fun B => B x y) hB
  let L : (Fin 11 → ZMod 2) →ₗ[ZMod 2] (ZMod 2) :=
    { toFun := fun x => co1ResidueM22QuadraticExpansion Q x - Q x
      map_add' := fun x y => by
        rw [QuadraticMap.map_add (co1ResidueM22QuadraticExpansion Q) x y,
          QuadraticMap.map_add Q x y, hp]
        abel
      map_smul' := fun a x => by
        have ha : a * a = a := by fin_cases a <;> decide +kernel
        simp only [QuadraticMap.map_smul, ha, smul_sub, RingHom.id_apply] }
  have hLa (x : Fin 11 → ZMod 2) :
      L x = co1ResidueM22QuadraticExpansion Q x - Q x := rfl
  have hLu (i : Fin 11) : L (co1ResidueM22QuadraticUnit i) = 0 := by
    rw [hLa, expansion_unit, sub_self]
  have hL : L = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 11)).ext
    intro i
    have hi : (Pi.basisFun (ZMod 2) (Fin 11)) i = co1ResidueM22QuadraticUnit i :=
      Pi.basisFun_apply (ZMod 2) (Fin 11) i
    rw [hi, LinearMap.zero_apply]
    exact hLu i
  apply QuadraticMap.ext
  intro x
  have he := DFunLike.congr_fun hL x
  rw [hLa, LinearMap.zero_apply] at he
  exact sub_eq_zero.mp he

/-- Vanishing on the original 231 point-coordinate rows forces every binary quadratic to vanish. -/
theorem co1ResidueM22QuadraticMap_zero
    (Q : QuadraticMap (ZMod 2) (Fin 11 → ZMod 2) (ZMod 2))
    (hzero : ∀ i : Fin 231, Q
      (monsterCo1GeometryBinaryMaskDecode (n := 11) (co1ResidueM22LinearCoordinates i)) = 0) :
    Q = 0 := by
  have hc : co1ResidueM22QuadraticCoefficients Q = 0 :=
    co1ResidueM22Quadratic_coefficients_zero _ (fun i => by
      rw [← co1ResidueM22QuadraticExpansion_apply, co1ResidueM22QuadraticExpansion_eq]
      exact hzero i)
  rw [← co1ResidueM22QuadraticExpansion_eq Q, co1ResidueM22QuadraticExpansion, hc]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
