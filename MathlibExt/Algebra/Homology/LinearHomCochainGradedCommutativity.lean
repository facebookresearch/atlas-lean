/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyCommutativity
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingBraiding
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHomotopy

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

@[simp]
private lemma moduleHom_comp_apply {B C D : ModuleCat.{u} R}
    (f : B ⟶ C) (g : C ⟶ D) (b : B) :
    (f ≫ g).hom b = g.hom (f.hom b) := rfl

@[simp]
private lemma moduleHom_zsmul_apply {B C : ModuleCat.{u} R}
    (z : ℤ) (f : B ⟶ C) (b : B) :
    (z • f).hom b = z • f.hom b := rfl

/-- A homotopy-cocommutative chain diagonal and a commutative coefficient
monoid induce a Koszul graded-commutative product on linear Hom-cohomology. -/
theorem linearHomCochainGradedPairing_comm_mk_of_homotopy
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [HasTensor K K]
    (A : ModuleCat.{u} R) [MonObj A] [IsCommMonObj A]
    (Δ : K ⟶ tensorObj K K)
    (hΔ : Homotopy
      (Δ ≫ (koszulTensorBraidingIso K K).hom) Δ)
    (p q : ℕ)
    (x : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).homology p)
    (y : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).homology q) :
    (GradedMonoid.mk (p + q)
        (((linearHomCochainGradedPairing R Δ (MonObj.mul (X := A))).pairHomology
          p q).hom (x ⊗ₜ[R] y)) :
      GradedMonoid (fun n ↦
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
          (op K)).homology n)) =
      ((-1 : ℤ) ^ (p * q)) •
        GradedMonoid.mk (q + p)
          (((linearHomCochainGradedPairing R Δ (MonObj.mul (X := A))).pairHomology
            q p).hom (y ⊗ₜ[R] x)) := by
  let Γ := Δ ≫ (koszulTensorBraidingIso K K).hom
  let PΔ := linearHomCochainGradedPairing R Δ (MonObj.mul (X := A))
  let PΓ := linearHomCochainGradedPairing R Γ (MonObj.mul (X := A))
  have hpair : ∀
      (φ : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p)
      (ψ : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q),
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
        (op K)).XIsoOfEq (Nat.add_comm p q)).hom.hom
          ((PΓ.pair p q).hom (φ ⊗ₜ[R] ψ)) =
        ((-1 : ℤ) ^ (p * q)) • (PΔ.pair q p).hom (ψ ⊗ₜ[R] φ) := by
    intro φ ψ
    have h := ConcreteCategory.congr_hom
      (linearHomCochainPair_koszul_swap R Δ
        (MonObj.mul (X := A)) (MonObj.mul (X := A))
        (IsCommMonObj.mul_comm A) q p) (ψ ⊗ₜ[R] φ)
    simpa only [moduleHom_comp_apply, moduleHom_zsmul_apply,
      ModuleCat.MonoidalCategory.braiding_hom_apply,
      Γ, PΓ, PΔ, Nat.mul_comm] using h
  have hcomm := CochainGradedPairing.pairHomology_comm_mk_of_pair
    R PΓ PΔ ((-1 : ℤ) ^ (p * q)) p q hpair x y
  have hpairs : PΓ.pairHomology p q = PΔ.pairHomology p q := by
    exact linearHomCochainGradedPairing_pairHomology_eq_of_homotopy
      R Γ Δ hΔ (MonObj.mul (X := A)) p q
  rw [hpairs] at hcomm
  exact hcomm

end HomologicalComplex
