/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyCommutativity
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingBraiding
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHomotopy

/-!
# Koszul commutativity of Hom cohomology pairings

Let R be commutative and K a nonnegative R-module chain complex, with all carriers in universe
u. Let A be a commutative monoid object in R-modules, with multiplication μ, and Δ:K→K⊗K a chain
map. Assume Δ followed by the Koszul chain braiding is homotopic to Δ.

The induced cohomology pairing on D=Hom_R(K,A) then satisfies x∪y=(-1)^{pq}y∪x for
x∈H^pD,y∈H^qD, with the two degree labels p+q and q+p compared in the graded carrier. The sign
comes from the chain Koszul interchange, while μ is commutative under ordinary coefficient
interchange. The statement concerns this specified pairing and homotopy condition.
-/

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

/-- Let R be commutative in universe u, with all module carriers and nonnegative chain terms in u.
Let K be a chain complex, A a commutative monoid object with multiplication μ, and Δ:K→K⊗K a
chain map with Homotopy(Δ≫b_{K,K}.hom,Δ) for the Koszul chain braiding b. Put D=Hom_R(K,A). For
x∈H^pD and y∈H^qD, the homogeneous classes satisfy ⟨p+q,cup_Δ(x,y)⟩=(-1)^{pq}•⟨q+p,cup_Δ(y,x)⟩
in the graded carrier, where cup_Δ is induced by Δ and μ. The equality retains both degree tags. -/
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
