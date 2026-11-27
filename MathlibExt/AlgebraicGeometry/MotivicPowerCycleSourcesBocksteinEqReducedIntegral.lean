/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPowerDescentModels
public import MathlibExt.AlgebraicGeometry.MotivicBocksteinModels

/-!
# The mod-ℓ Bockstein as a reduced integral boundary

Naturality of the native coefficient mapping cones identifies the mod-ℓ Bockstein
with reduction of the integral Bockstein on reduced motivic cohomology.

Source: Vladimir Voevodsky, *Reduced power operations in motivic cohomology*,
arXiv:math/0107109v1, §6 and §8 for the integral and mod-ℓ connecting maps; the comparison
is the naturality of these connecting maps along reduction modulo ℓ.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open MotivicFinitePermutationModels MotivicPermutationBundleModels
open MotivicFinitePowerCycles MotivicPowerQuotientModels MotivicPowerDescentModels
open MotivicBocksteinModels PointedMotivicModels ReducedMotivicCohomologyModels
open NisnevichTransferModels EffectiveMotivicComplexModels MotivicTorusClassModels

open CochainComplex.HomComplex

private theorem coneBoundary_natural {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C]
    (s t : ShortComplex (CochainComplex C ℤ)) (a : s ⟶ t)
    (e₁ : DerivedCategory.Q.obj (CochainComplex.mappingCone s.f) ≅
      DerivedCategory.Q.obj s.X₃)
    (e₂ : DerivedCategory.Q.obj (CochainComplex.mappingCone t.f) ≅
      DerivedCategory.Q.obj t.X₃)
    (h₁ : e₁.hom = DerivedCategory.Q.map (CochainComplex.mappingCone.desc s.f 0 s.g
      (by simp only [δ_zero, s.zero, Cochain.ofHom_zero])))
    (h₂ : e₂.hom = DerivedCategory.Q.map (CochainComplex.mappingCone.desc t.f 0 t.g
      (by simp only [δ_zero, t.zero, Cochain.ofHom_zero]))) :
    DerivedCategory.Q.map a.τ₃ ≫ e₂.inv ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle t.f).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app t.X₁ =
      e₁.inv ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.triangle s.f).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app s.X₁ ≫
        (DerivedCategory.Q.map a.τ₁)⟦(1 : ℤ)⟧' := by
  have hc : e₁.hom ≫ DerivedCategory.Q.map a.τ₃ =
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.map s.f t.f a.τ₁ a.τ₂ a.comm₁₂.symm) ≫ e₂.hom := by
    rw [h₁, h₂, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (CochainComplex.mappingCone.descShortComplex_naturality a).symm
  have ht := (DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap s.f t.f a.τ₁ a.τ₂ a.comm₁₂.symm)).comm₃
  dsimp [Functor.mapTriangle, CochainComplex.mappingCone.triangleMap] at ht
  apply (cancel_epi e₁.hom).1
  rw [← Category.assoc e₁.hom (DerivedCategory.Q.map a.τ₃), hc]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ht.symm

private def sequenceComparison (ell : ℕ) : integralSequence ell ⟶ modSequence ell where
  τ₁ := integralReduction ell
  τ₂ := integralReduction (ell * ell)
  τ₃ := 𝟙 _
  comm₁₂ := by
    ext z
    apply ULift.ext
    change modInjectionAdd ell (z.down : ZMod ell) =
      (((ell : ℤ) * z.down : ℤ) : ZMod (ell * ell))
    rw [modInjectionAdd, ZMod.lift_coe]
    simp
  comm₂₃ := by
    ext z
    apply ULift.ext
    change (ZMod.castHom (dvd_mul_right ell ell) (ZMod ell))
      (z.down : ZMod (ell * ell)) = (z.down : ZMod ell)
    simp

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- The mod-ℓ Bockstein is the reduction of the integral Bockstein: for a prime ℓ, the given
coefficient complex system `B` (over a field $k$, with Nisnevich sheafification and the
correspondence laws and additivity), the reduced free Nisnevich system `F`, a pointed space $X$,
integers $p, q$, and cone data `I` and `M` in weight $q$ for the sequences
$\mathbb{Z} \to \mathbb{Z} \to \mathbb{Z}/\ell$ and
$\mathbb{Z}/\ell \to \mathbb{Z}/\ell^2 \to \mathbb{Z}/\ell$, every class $u$ in reduced motivic
cohomology $\tilde H^{p,q}(X; \mathbb{Z}/\ell)$ satisfies $\beta(u) = \rho(\delta(u))$, where
$\beta$ is the connecting map of the second sequence, $\delta$ that of the first, and $\rho$ is
reduction modulo ℓ. -/
theorem bockstein_eq_reduced_integral {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
    (ell : ℕ) [Fact ell.Prime]
    (F : ReducedFreeNisSystem k) (X : PointedSpaces (k := k)) (p q : ℤ)
    (I : CoefficientConeSource B (integralSequence ell) q)
    (M : CoefficientConeSource B (modSequence ell) q)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    bockstein B ell F X p q M u =
      ReducedMotivicCohomologyModels.coefficientMap B F X (p + 1) q
        (integralReduction ell) (integralBockstein B ell F X p q I u)
    := by
  let s : ShortComplex (CochainComplex (NisModules (k := k)) ℤ) :=
    ShortComplex.mk (firstMap B (integralSequence ell) q)
      (secondMap B (integralSequence ell) q) I.zero
  let t : ShortComplex (CochainComplex (NisModules (k := k)) ℤ) :=
    ShortComplex.mk (firstMap B (modSequence ell) q)
      (secondMap B (modSequence ell) q) M.zero
  let a : s ⟶ t := {
    τ₁ := (B.weightFunctor q).map (sequenceComparison ell).τ₁
    τ₂ := (B.weightFunctor q).map (sequenceComparison ell).τ₂
    τ₃ := (B.weightFunctor q).map (sequenceComparison ell).τ₃
    comm₁₂ := by
      simpa only [s, t, firstMap, secondMap, Functor.map_comp] using
        congrArg (B.weightFunctor q).map (sequenceComparison ell).comm₁₂
    comm₂₃ := by
      simpa only [s, t, firstMap, secondMap, Functor.map_comp] using
        congrArg (B.weightFunctor q).map (sequenceComparison ell).comm₂₃ }
  let : QuasiIso (coefficientConeComparison B (integralSequence ell) q I.zero) := I.quasi
  let : QuasiIso (coefficientConeComparison B (modSequence ell) q M.zero) := M.quasi
  have h := coneBoundary_natural s t a
    (asIso (DerivedCategory.Q.map
      (coefficientConeComparison B (integralSequence ell) q I.zero)))
    (asIso (DerivedCategory.Q.map
      (coefficientConeComparison B (modSequence ell) q M.zero))) rfl rfl
  have ha₃ : a.τ₃ = 𝟙 _ := (B.weightFunctor q).map_id _
  rw [ha₃, CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hb : coefficientBoundary B M = coefficientBoundary B I ≫
      (DerivedCategory.Q.map ((B.weightFunctor q).map (integralReduction ell)))⟦(1 : ℤ)⟧' := by
    simpa only [a, sequenceComparison, coefficientBoundary, s, t, Category.assoc] using h
  change coefficientConnecting B F X p q M u =
    ReducedMotivicCohomologyModels.coefficientMap B F X (p + 1) q
      (integralReduction ell) (coefficientConnecting B F X p q I u)
  unfold coefficientConnecting
    ReducedMotivicCohomologyModels.coefficientMap
  rw [hb]
  dsimp only [integralSequence, modSequence]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f => u ≫ (coefficientBoundary B I)⟦p⟧' ≫ f)
    ((shiftFunctorAdd' _ (1 : ℤ) p (p + 1) (by omega)).inv.naturality
      (DerivedCategory.Q.map ((B.weightFunctor q).map (integralReduction ell))))

end WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted
