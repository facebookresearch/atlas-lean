/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientHeightComparison

/-!
# Universe lifting of enveloping resolutions and coefficient homology

Let R be a commutative ring, L an R-Lie algebra, and U = U_R(L). The twice-lifted enveloping
Chevalley–Eilenberg complex is isomorphic to its single lift at the combined carrier universe.
If L is free over R, this isomorphism commutes with the augmentations of the lifted projective
resolutions of the trivial U-module.

For an L-module M, let N_H be the right enveloping representation of its coefficient lift.
Balanced tensor cancellation identifies N_H ⊗_U Q_H with C_*(L;M_H), where Q_H is the lifted
enveloping resolution. This cancellation and the resulting homology-to-Tor comparison commute
with coefficient and whole-output height transport.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z t a b c

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex coefficientComplexULift HomologicalComplex.homologyFunctor
  rawLieCoefficientLiftAt

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

local instance rawResolutionHeight_input_preservesHomology {A : Type a} [Ring A] :
    (ModuleCat.uliftFunctor.{c, b} A).PreservesHomology := Functor.preservesHomologyOfExact _

/-- Let R be a commutative ring, L an R-Lie algebra, and U = U_R(L). Put H = max(u,v,v′,w,w′,z)
and H′ = max(H,t), and let Q be the enveloping Chevalley–Eilenberg complex in shape down ℕ. If
I_H lifts U-modules to H and I lifts them from H to H′, repeated-lift flattening gives
I(I_H(Q)) ≅ I_H′(Q). Its degreewise map sends up(up(q)) to up(q), and its inverse adds the
intermediate lift. This chain isomorphism does not require L to be free. -/
def rawEnvelopingComplexHeightIso :
    ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((envelopingLiftFunctor.{u, v, max u v v' w w' z} R L).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (envelopingComplex R L)) ≅
      (((envelopingLiftFunctor.{u, v, max u v v' w w' z t} R L).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (envelopingComplex R L)) :=
  ((Functor.mapHomologicalComplexCompIso
    (F := envelopingLiftFunctor.{u, v, max u v v' w w' z} R L)
      (G := (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L))
    (Iso.refl _) (ComplexShape.down ℕ)).app (envelopingComplex R L)) ≪≫
      ((NatIso.mapHomologicalComplex
        (ModuleCat.uliftFunctorCompIso.{max u v v' w w' z, max u v v' w w' z t, max u v} U)
          (ComplexShape.down ℕ)).app (envelopingComplex R L))

theorem rawEnvelopingComplexHeightIso_inv_up (n : ℕ) (x : (envelopingComplex R L).X n) :
    ((rawEnvelopingComplexHeightIso.{u, v, v', w, w', z, t} R L).inv.f n).hom (ULift.up x) =
      ULift.up (ULift.up x) := rfl

section Resolution

variable [Module.Free R L]


/-- Let R be a commutative ring and L an R-Lie algebra that is free as an R-module. Put U =
U_R(L), H = max(u,v,v′,w,w′,z), and H′ = max(H,t). Let Q_H → T_H and Q_H′ → T_H′ be the lifted
enveloping projective resolutions of the augmentation module, χ : I(Q_H) ≅ Q_H′ the
repeated-lift flattening, and τ : I(T_H) ≅ T_H′ its augmentation-module counterpart. Then
χ.inv ≫ I(π_H) = π_H′ ≫ single₀(τ.inv), where the augmentation maps have target the complexes
concentrated in degree zero. Thus the inverse flattening is a morphism of augmented complexes. -/
theorem rawEnvelopingComplexHeightIso_inv_augmentation :
    (rawEnvelopingComplexHeightIso.{u, v, v', w, w', z, t} R L).inv ≫
      Functor.mapChainAugmentation (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
        (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).π =
    (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L).π ≫
      (ChainComplex.single₀ (ModuleCat.{max u v v' w w' z t} U)).map
      (rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L).inv := by
  apply (ChainComplex.toSingle₀Equiv (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L).complex
    ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj
      (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L))).injective
  apply Subtype.ext
  change ((rawEnvelopingComplexHeightIso.{u, v, v', w, w', z, t} R L).inv.f 0) ≫
    (Functor.mapChainAugmentation (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
      (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).π).f 0 =
      (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L).π.f 0 ≫
        (rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L).inv
  rw [Functor.mapChainAugmentation_f_zero, liftedEnvelopingProjectiveResolution_π_f_zero,
    liftedEnvelopingProjectiveResolution_π_f_zero]
  apply ModuleCat.hom_ext
  ext x
  cases x
  rfl

variable (M : LieModuleCat.{w} R L)


local instance rawResolutionHeight_low_additive {A : Type a} [Ring A] [Algebra R A]
    (N : ModuleCat.{b} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, a, b, c} R A N).Additive :=
  ModuleCat.BalancedTensor.additive R A N

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), U = U_R(L), Q_H the lifted enveloping projective resolution of the
augmentation module, and N_H the right representation of M_H with m·ι(x) = −[x,m]. There is a
chain isomorphism N_H ⊗_U Q_H ≅ C_*(L;M_H). In degree n the balanced class [m,up(a ⊗ b)] maps
to a ⊗ (m·b), for a ∈ Λⁿ_R L and b ∈ U. The coefficient complex is in exterior-first order and
the action is the right U-action. -/
def rawTensorCoefficientComplexIsoAt :
    ((ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex ≅
      coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) :=
  rightTensorCoefficientIsoAt.{u, v, v', max w w' z} R L
    (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) ≪≫
    (nativeRightCoefficientComplexIso.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).symm

theorem rawTensorCoefficientComplexIsoAt_mk_tmul (n : ℕ)
  (m : (LieModuleCat.RightUniversalEnveloping.representObj R L
  (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))) (x : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    ((rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M).hom.f n).hom
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex.X n)) m
          (ULift.up (x ⊗ₜ[R] a))) = x ⊗ₜ[R]
            (show (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) from MulOpposite.op a • m) := by
  change
    ((nativeRightCoefficientComplexIso.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).inv.f n).hom
    (rightTensorCoordinatesAt.{u, v, v', max w w' z} R L
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      n
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex.X n)) m
          (ULift.up (x ⊗ₜ[R] a)))) = _
  rw [rightTensorCoordinatesAt_mk_tmul]
  rfl

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), U = U_R(L), F_H(X) = N_H ⊗_U X, and V = ULift_{H→H′} on
R-modules. For the lifted enveloping resolutions Q_H and Q_H′, define F_H′(Q_H′) → V(F_H(Q_H))
by applying F_H′ to the inverse χ.inv of the resolution-lift flattening χ : I_U(Q_H) ≅ Q_H′,
then applying the tensor height natural transformation F_H′∘I_U → V∘F_H. This specifies a
chain map in every degree. -/
def rawTensorResolutionHeightMap :
    ((ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L).complex ⟶
      ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex) :=
  ((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (rawEnvelopingComplexHeightIso.{u, v, v', w, w', z, t} R L).inv ≫
      (Functor.mapSquareHomologicalComplex (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
        (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R)
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R)
        (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M).hom).app
          (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and V = ULift_{H→H′}. Let e_H : N_H ⊗_U Q_H ≅ C_*(L;M_H)
and e_H′ be the tensor cancellation isomorphisms, d : N_H′ ⊗_U Q_H′ → V(N_H ⊗_U Q_H) the
resolution height map, and k : C_*(L;M_H′) ≅ V(C_*(L;M_H)) the coefficient height isomorphism.
Then d ≫ V(e_H.hom) = e_H′.hom ≫ k.hom. Both composites use the right enveloping action in the
formula [m,a ⊗ b] ↦ a ⊗ (m·b). -/
theorem rawTensorCoefficientComplexIsoAt_height :
    rawTensorResolutionHeightMap.{u, v, v', w, w', z, t} R L M ≫
      ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M).hom =
    (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', max z t} R L M).hom ≫
      (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.Balanced.hom_ext
  intro m p
  let N₀ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)
  let P₀ := liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L
  let P₁ := liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L
  let V := rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R
  letI : Module R (P₁.complex.X n) := Module.compHom (P₁.complex.X n) (algebraMap R U)
  let A := ((rawTensorResolutionHeightMap.{u, v, v', w, w', z, t} R L M ≫
    (V.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M).hom).f n).hom.comp
        (TensorProduct.Balanced.mk R U N₁ (P₁.complex.X n) m)
  let B := (((rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', max z t} R L M).hom ≫
    (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M).hom).f n).hom.comp
      (TensorProduct.Balanced.mk R U N₁ (P₁.complex.X n) m)
  change A p = B p
  cases m with
  | up m =>
      cases p with
      | up p =>
          induction p using TensorProduct.induction_on with
          | zero =>
              change A 0 = B 0
              exact A.map_zero.trans B.map_zero.symm
          | add p q hp hq =>
              change A (ULift.up p + ULift.up q) = B (ULift.up p + ULift.up q)
              exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hp hq).trans
                (B.map_add _ _).symm)
          | tmul x a =>
              let X := P₀.complex.X n
              let p₀ : X := ULift.up (x ⊗ₜ[R] a)
              let e₀ := (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M).hom.f n
              let e₁ := (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', max z t} R L M).hom.f n
              have hHeight := rawTensorHeightEquiv_mk_up.{u, v, v', w, w', z, t} R L M X m p₀
              have hLow := rawTensorCoefficientComplexIsoAt_mk_tmul.{u, v, v', w, w', z} R L M n
                (show N₀ from ULift.up m) x a
              have hHigh := rawTensorCoefficientComplexIsoAt_mk_tmul.{u, v, v', w, w', max z t} R L M n
                (show N₁ from ULift.up m) x a
              have hCE := rawCoefficientComplexHeightDegreeEquiv_tmul.{u, v, v', w, w', z, t} R L M n x
                (show rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M from @SMul.smul Uᵐᵒᵖ N₁
                  N₁.isModule.toDistribMulAction.toMulAction.toSMul
                  (MulOpposite.op (show U from a)) (ULift.up m))
              have hAct := (rawRightCoefficientHeightEquiv.{u, v, v', w, w', z, t} R L M).map_smul
                (MulOpposite.op a) (show N₁ from ULift.up m)
              let q := rawTensorHeightEquiv.{u, v, v', w, w', z, t} R L M X
                (TensorProduct.Balanced.mk R U N₁
                  ((ModuleCat.restrictScalars (algebraMap R U)).obj
                    ((rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L).obj X))
                      (ULift.up m) (ULift.up p₀))
              have hDown : q.down = TensorProduct.Balanced.mk R U N₀
                  ((ModuleCat.restrictScalars (algebraMap R U)).obj X) (ULift.up m) p₀ :=
                congrArg ULift.down hHeight
              change ULift.up (e₀.hom q.down) =
                rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n
                  (e₁.hom (TensorProduct.Balanced.mk R U N₁
                    ((ModuleCat.restrictScalars (algebraMap R U)).obj (P₁.complex.X n))
                      (ULift.up m) (ULift.up (x ⊗ₜ[R] a))))
              have hLeft := (congrArg (fun q => ULift.up (e₀.hom q)) hDown).trans
                (congrArg ULift.up hLow)
              have hRight := (congrArg
                (rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n) hHigh).trans hCE
              let M₀ := rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M
              letI : Module R M₀ := M₀.moduleStructure
              exact hLeft.trans ((congrArg (fun q : M₀ => ULift.up (x ⊗ₜ[R] q)) hAct.symm).trans hRight.symm)

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), U = U_R(L), F_H(X) = N_H ⊗_U X, and Q_H the lifted enveloping projective
resolution of the augmentation module T_H. Let e_H : F_H(Q_H) ≅ C_*(L;M_H) be tensor
cancellation. For every n ∈ ℕ, the comparison H_n(C_*(L;M_H)) → (L_nF_H)(T_H) is H_n(e_H.inv)
followed by the inverse of Q_H.isoLeftDerivedObj(F_H,n). This fixes its direction from
coefficient homology to the left-derived balanced tensor. -/
theorem nativeCoefficientHomologyIsoTor_eq_rawTensorCoordinates (n : ℕ) :
    (nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
      n).hom =
      HomologicalComplex.homologyMap
        (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M).inv n ≫
          ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).isoLeftDerivedObj
            (ModuleCat.BalancedTensor.functor R U
            (LieModuleCat.RightUniversalEnveloping.representObj R L
            (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
            ModuleCat.{max u v v' w w' z} R) n).inv := by
  let N₀ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  let e := nativeRightCoefficientComplexIso.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  let q := rightTensorCoefficientIsoAt.{u, v, v', max w w' z} R L N₀
  let P := liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L
  let F : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R :=
    ModuleCat.BalancedTensor.functor R U N₀
  have hNative : (nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n).hom =
      (HomologicalComplex.homologyMap e.hom n ≫ HomologicalComplex.homologyMap q.inv n) ≫
        (P.isoLeftDerivedObj F n).inv := by
    exact (Category.assoc _ _ _).symm
  have hInverse : (rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M).inv = e.hom ≫ q.inv := rfl
  have hMap := HomologicalComplex.homologyMap_comp e.hom q.inv n
  exact hNative.trans (congrArg (fun h => h ≫ (P.isoLeftDerivedObj F n).inv)
    ((congrArg (fun h => HomologicalComplex.homologyMap h n) hInverse).trans hMap).symm)

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and V = ULift_{H→H′}. For n ∈ ℕ, let Φ_H : H_n(C_*(L;M_H))
≅ Tor_H,n(M) and Φ_H′ be the comparisons obtained from the lifted enveloping resolutions. Let
e : H_n(C_*(L;M_H′)) ≅ V(H_n(C_*(L;M_H))) be coefficient height transport, and J :
V(Tor_H,n(M)) ≅ Tor_H′,n(M) the derived tensor height isomorphism. Then Φ_H′.hom ≫ J.inv =
e.hom ≫ V(Φ_H.hom). -/
theorem nativeCoefficientHomologyIsoTor_raw_height (n : ℕ) :
    (nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z t} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M) n).hom ≫
      (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv =
    (rawCoefficientLiftHomologyHeightIso.{u, v, v', w, w', z, t} R L M n).hom ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n).hom := by
  let e₀ := rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', z} R L M
  let e₁ := rawTensorCoefficientComplexIsoAt.{u, v, v', w, w', max z t} R L M
  let d := rawTensorResolutionHeightMap.{u, v, v', w, w', z, t} R L M
  let c := rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M
  let mV := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
    (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
  have h : e₁.inv ≫ d = c.hom ≫
    ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map e₀.inv
    := by
    let G := (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)
    apply (cancel_mono (G.map e₀.hom)).1
    have hCancel : G.map e₀.inv ≫ G.map e₀.hom = 𝟙 _ :=
      (G.map_comp _ _).symm.trans ((congrArg G.map e₀.inv_hom_id).trans (G.map_id _))
    have hSquare := rawTensorCoefficientComplexIsoAt_height.{u, v, v', w, w', z, t} R L M
    have hLeft : (e₁.inv ≫ d) ≫ G.map e₀.hom = c.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => e₁.inv ≫ q) hSquare).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ c.hom) e₁.inv_hom_id).trans (Category.id_comp _))))
    have hRight : (c.hom ≫ G.map e₀.inv) ≫ G.map e₀.hom = c.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => c.hom ≫ q) hCancel).trans (Category.comp_id _))
    exact hLeft.trans hRight.symm
  have hH : HomologicalComplex.homologyMap e₁.inv n ≫ HomologicalComplex.homologyMap d n =
      HomologicalComplex.homologyMap c.hom n ≫ HomologicalComplex.homologyMap
        (((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
          e₀.inv) n := by
    exact (HomologicalComplex.homologyMap_comp e₁.inv d n).symm.trans
      ((congrArg (fun a => HomologicalComplex.homologyMap a n) h).trans
        (HomologicalComplex.homologyMap_comp c.hom _ n))
  have hNat : HomologicalComplex.homologyMap
      (((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        e₀.inv) n ≫
        mV.hom.app
          (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex) =
      mV.hom.app (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) ≫
        (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (HomologicalComplex.homologyMap e₀.inv n) :=
    mV.hom.naturality e₀.inv
  rw [rawLieCoefficientTorHeightIsoAt_inv,
    Functor.leftDerivedSquareHom_eq_with_source_lift (rawTensorHeightSourceLift.{u, v, v', w, w', z, t} R L)
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
      (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
      ModuleCat.{max u v v' w w' z t} R)
      (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
      : ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R)
      (rawTensorHeightNatIso.{u, v, v', w, w', z, t} R L M).hom n
      (rawEnvelopingTrivialHeightIso.{u, v, v', w, w', z, t} R L).inv
        (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L)
        (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L)
      (rawEnvelopingComplexHeightIso.{u, v, v', w, w', z, t} R L).inv
      (rawEnvelopingComplexHeightIso_inv_augmentation.{u, v, v', w, w', z, t} R L),
    nativeCoefficientHomologyIsoTor_eq_rawTensorCoordinates,
    nativeCoefficientHomologyIsoTor_eq_rawTensorCoordinates]
  change
    (HomologicalComplex.homologyMap e₁.inv n ≫
    ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L).isoLeftDerivedObj
    (ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
    ModuleCat.{max u v v' w w' z t} R) n).inv) ≫
      (((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z t} R L).isoLeftDerivedObj
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) : ModuleCat.{max u v v' w w' z t} U ⥤
        ModuleCat.{max u v v' w w' z t} R) n).hom ≫ HomologicalComplex.homologyMap d n ≫
        mV.hom.app
          (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).complex) ≫
          (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
            ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).isoLeftDerivedObj
            (ModuleCat.BalancedTensor.functor R U
            (LieModuleCat.RightUniversalEnveloping.representObj R L
            (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
            ModuleCat.{max u v v' w w' z} R) n).inv) =
    (HomologicalComplex.homologyMap c.hom n ≫ mV.hom.app
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))) ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (HomologicalComplex.homologyMap e₀.inv n ≫
        ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w w' z} R L).isoLeftDerivedObj
        (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R) n).inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [← Category.assoc (HomologicalComplex.homologyMap e₁.inv n), hH]
  simp only [Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap
    (((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map e₀.inv)
      n), hNat]
  simp only [Category.assoc]

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and V = ULift_{H→H′}. For n ∈ ℕ, let Ψ_H :
ULift_H(H_n(C_*(L;M))) ≅ Tor_H,n(M) and Ψ_H′ be the transported homology-to-Tor comparisons.
Let b : V(ULift_H(H_n(C_*(L;M)))) ≅ ULift_H′(H_n(C_*(L;M))) flatten the repeated homology
lift, and J : V(Tor_H,n(M)) ≅ Tor_H′,n(M) be the Tor height isomorphism. Then Ψ_H′.hom ≫ J.inv
= b.inv ≫ V(Ψ_H.hom). -/
theorem rawCoefficientHomologyIsoTorAt_height (n : ℕ) :
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', max z t} R L M n).hom ≫
      (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv =
    (rawOriginalCoefficientHomologyHeightIso.{u, v, v', w, w', z, t} R L M n).inv ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom := by
  let A := rawCoefficientHomologyTransportAt.{u, v, v', w, w', max z t} R L M n
  let B := rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M n
  let T := nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z t} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M) n
  let S := nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n
  let V := rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R
  let b := rawOriginalCoefficientHomologyHeightIso.{u, v, v', w, w', z, t} R L M n
  have hHigh : (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', max z t} R L M n).hom =
      A.hom ≫ T.hom := rfl
  have hLow : (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom =
      B.hom ≫ S.hom := rfl
  have hNat : T.hom ≫ (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv =
      (rawCoefficientLiftHomologyHeightIso.{u, v, v', w, w', z, t} R L M n).hom ≫ V.map S.hom :=
    nativeCoefficientHomologyIsoTor_raw_height.{u, v, v', w, w', z, t} R L M n
  have hTransport := rawCoefficientHomologyTransportAt_height.{u, v, v', w, w', z, t} R L M n
  let c := rawCoefficientLiftHomologyHeightIso.{u, v, v', w, w', z, t} R L M n
  let h := rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n
  have hMid : (A.hom ≫ T.hom) ≫ h.inv = b.inv ≫ V.map (B.hom ≫ S.hom) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => A.hom ≫ q) hNat).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ V.map S.hom) hTransport).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun q => b.inv ≫ q) (V.map_comp B.hom S.hom).symm)))))
  exact (congrArg (fun q => q ≫ h.inv) hHigh).trans
    (hMid.trans (congrArg (fun q => b.inv ≫ V.map q) hLow.symm))

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and let E_H : H_n(C_*(L;M)) ≃ₗ[R] Tor_H,n(M) and E_H′ be
the comparisons with the unlifted homology carrier. For n ∈ ℕ and a ∈ H_n(C_*(L;M)), the
inverse Tor height isomorphism J : ULift_{H′}(Tor_H,n(M)) ≅ Tor_H′,n(M) satisfies
J.inv(E_H′(a)) = up(E_H(a)). The input class a is unchanged; the output is the lift of its
lower-height Tor value. -/
theorem rawCoefficientHomologyEquivTorAt_height (n : ℕ)
    (a : (coefficientComplex R L M).homology n) :
    (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv
      (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', max z t} R L M n a) =
    ULift.up (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n a) := by
  have h := congrArg (fun f => f.hom (ULift.up a))
    (rawCoefficientHomologyIsoTorAt_height.{u, v, v', w, w', z, t} R L M n)
  change (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv.hom
      ((rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', max z t} R L M n).hom (ULift.up a)) =
    ULift.up ((rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom (ULift.up a)) at h
  simpa only [rawCoefficientHomologyEquivTorAt_apply] using h

end Resolution

end ChevalleyEilenberg
