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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientResolutionHeight
public import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyOpcycles

/-!
# Degree-zero Lie homology and the augmentation tensor

Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Write U = U_R(L), let N be
the right U-module with m·ι(x) = −[x,m], and let T be the augmentation module, with scalar
carrier ULift(R). The degree-zero Chevalley–Eilenberg class of 1 ⊗ m corresponds to the
balanced class [m,up(1)] in N ⊗_U T.

This identification holds without freeness of L and is compatible with coefficient and
whole-output universe lifts. When L is free over R, the degree-zero homology-to-Tor comparison
followed by the derived-zero map and the input and coefficient lift cancellations equals this
identification.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z a b c

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex coefficientComplexULift HomologicalComplex.homologyFunctor
  rawLieCoefficientLiftAt

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (M : LieModuleCat.{w} R L)

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put H =
max(u,v,v′,w,w′,z), where R, L, and M have universes u, v, and w. Let cl_M(m) ∈ H₀(C_*(L;M))
be the class of 1 ⊗ m, where 1 is the empty exterior product in Λ⁰_R L. The homology transport
T_H : ULift_H(H₀(C_*(L;M))) ≅ H₀(C_*(L;M_H)) sends up(cl_M(m)) to cl_M_H(up(m)). The class is
formed using the degree-zero opcycles projection and the canonical identification of opcycles
with homology. -/
theorem rawCoefficientHomologyTransportAt_zero_class (m : M) :
    (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom
      (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))) =
    (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).isoHomologyι₀.inv
      ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).pOpcycles 0
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R]
          (ULift.up m : (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)))) := by
  let K := coefficientComplex R L M
  let Q := coefficientComplexULift.{u, v, w, max u v v' w w' z} R L M
  let W := ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R
  letI : W.PreservesHomology := Functor.preservesHomologyOfExact W
  let eH := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 0 W).app K
  let eO := (K.sc 0).mapOpcyclesIso W
  let E := coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M
  let p : K.X 0 := exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m
  have hp : W.map (K.pOpcycles 0) ≫ eO.inv = Q.pOpcycles 0 := by
    apply (cancel_mono eO.hom).1
    have hCancel : (W.map (K.pOpcycles 0) ≫ eO.inv) ≫ eO.hom = W.map (K.pOpcycles 0) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => W.map (K.pOpcycles 0) ≫ q) eO.inv_hom_id).trans (Category.comp_id _))
    exact hCancel.trans (ShortComplex.pOpcycles_comp_mapOpcyclesIso_hom (K.sc 0) W).symm
  have hι : W.map K.isoHomologyι₀.inv ≫ eH.inv = eO.inv ≫ Q.isoHomologyι₀.inv := by
    apply (cancel_mono Q.isoHomologyι₀.hom).1
    have hCancel : (eO.inv ≫ Q.isoHomologyι₀.inv) ≫ Q.isoHomologyι₀.hom = eO.inv :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => eO.inv ≫ q) Q.isoHomologyι₀.inv_hom_id).trans (Category.comp_id _))
    refine Eq.trans ?_ hCancel.symm
    change W.map K.isoHomologyι₀.inv ≫ ((K.sc 0).mapHomologyIso W).inv ≫
      ((K.sc 0).map W).homologyι = eO.inv
    have hInv := ShortComplex.mapHomologyIso_inv_comp_homologyι (K.sc 0) W
    have hMap : W.map K.isoHomologyι₀.inv ≫ W.map K.isoHomologyι₀.hom = 𝟙 _ :=
      (W.map_comp _ _).symm.trans
        ((congrArg W.map K.isoHomologyι₀.inv_hom_id).trans (W.map_id _))
    exact (congrArg (fun q => W.map K.isoHomologyι₀.inv ≫ q) hInv).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ eO.inv) hMap).trans (Category.id_comp _)))
  have hClass : W.map (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫ eH.inv =
      Q.pOpcycles 0 ≫ Q.isoHomologyι₀.inv := by
    exact (congrArg (fun q => q ≫ eH.inv) (W.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun q => W.map (K.pOpcycles 0) ≫ q) hι).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ Q.isoHomologyι₀.inv) hp))))
  have hLift := congrArg
    (fun f : W.obj (K.X 0) ⟶ Q.homology 0 => f.hom (ULift.up p)) hClass
  change eH.inv.hom (ULift.up (K.isoHomologyι₀.inv.hom ((K.pOpcycles 0).hom p))) =
    Q.isoHomologyι₀.inv.hom ((Q.pOpcycles 0).hom (ULift.up p)) at hLift
  have hEι := congrArg
    (fun f : Q.opcycles 0 ⟶ (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology 0 =>
      f.hom ((Q.pOpcycles 0).hom (ULift.up p)))
    (ChainComplex.isoHomologyι₀_inv_naturality E.hom)
  have hEp := congrArg
    (fun f : Q.X 0 ⟶ (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).opcycles 0 =>
      f.hom (ULift.up p))
    (HomologicalComplex.p_opcyclesMap E.hom 0)
  have hEx : (E.hom.f 0).hom (ULift.up p) =
      exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R]
        (ULift.up m : (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
    coefficientULiftDegreeEquiv_up_tmul R L M 0 _ m
  change (HomologicalComplex.homologyMap E.hom 0).hom
    (eH.inv.hom (ULift.up (K.isoHomologyι₀.inv.hom ((K.pOpcycles 0).hom p)))) = _
  rw [hLift]
  exact hEι.trans (congrArg
    (fun a : (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).opcycles 0 =>
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).isoHomologyι₀.inv.hom a)
    (hEp.trans
      (congrArg
      (fun a => ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).pOpcycles 0).hom a)
      hEx)))

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Write U = U_R(L), N for
the right U-module satisfying m·ι(x) = −[x,m], and T for its augmentation left module. For H =
max(u,v,v′,w,w′,z), let N_H represent the coefficient lift M_H. The coefficient equivalence
N_H ≃ N induces an R-linear equivalence N_H ⊗_U T ≃ₗ[R] N ⊗_U T. It sends [up(m),s] to [m,s]
and leaves the augmentation-module factor unchanged; its inverse lifts the coefficient
representative. -/
def rawCoefficientTrivialTensorEquiv :
    (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))).obj (envelopingTrivialObject R L) ≃ₗ[R]
      (ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L) :=
  by
    let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
    let N := LieModuleCat.RightUniversalEnveloping.representObj R L M
    let T := (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)
    let e := LieModuleCat.RightUniversalEnveloping.coefficientULiftGroundEquiv.{u, v, w,
      max u v v' w w' z} R L M
    have h : ∀ (a : U)
        (m : (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁),
        e (MulOpposite.op a • m) = MulOpposite.op a • e m :=
      fun a m => (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w,
        max u v v' w w' z} R L M).map_smul (MulOpposite.op a) m
    exact TensorProduct.Balanced.congr (k := R) (R := U)
      (M := (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁)
      (M' := (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N) (N := T) (N' := T)
      e (LinearEquiv.refl R T) h (fun _ _ => rfl)

@[simp]
theorem rawCoefficientTrivialTensorEquiv_mk_up (m : M) (x : envelopingTrivialObject R L) :
    rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          (ULift.up m) x) =
    TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
      ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m x := by
  let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  let N := LieModuleCat.RightUniversalEnveloping.representObj R L M
  let T := (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)
  let e := LieModuleCat.RightUniversalEnveloping.coefficientULiftGroundEquiv.{u, v, w,
    max u v v' w w' z} R L M
  have h : ∀ (a : U) (m : (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁),
      e (MulOpposite.op a • m) = MulOpposite.op a • e m :=
    fun a m => (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w,
      max u v v' w w' z} R L M).map_smul (MulOpposite.op a) m
  exact TensorProduct.Balanced.congr_mk e (LinearEquiv.refl R T) h (fun _ _ => rfl)
    (show (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁ from ULift.up m)
    (show T from x)

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put U = U_R(L), and let N
and N_H be the right enveloping representations of M and its coefficient lift to H =
max(u,v,v′,w,w′,z). For the augmentation module T, coefficient flattening followed by
whole-output lifting gives N_H ⊗_U T ≃ₗ[R] ULift_H(N ⊗_U T). The forward map is [up(m),s] ↦
up([m,s]); the inverse removes the outer output lift and lifts the coefficient representative. -/
def rawCoefficientTrivialTensorOutputLiftEquiv :
    (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))).obj (envelopingTrivialObject R L) ≃ₗ[R]
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
        ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L)) :=
  (rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M).trans
    (ULift.moduleEquiv : ULift.{max u v v' w w' z}
      ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
      (envelopingTrivialObject R L)) ≃ₗ[R]
      ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
      (envelopingTrivialObject R L))).symm

@[simp]
theorem rawCoefficientTrivialTensorOutputLiftEquiv_mk_up (m : M) (x : envelopingTrivialObject R L) :
    rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          (ULift.up m) x) =
    ULift.up (TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
      ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m x) := by
  exact congrArg ULift.up (rawCoefficientTrivialTensorEquiv_mk_up.{u, v, v', w, w', z} R L M m x)

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Set U = U_R(L), let N
represent the right action m·ι(x) = −[x,m], and let T be the augmentation module with carrier
ULift(R). For H = max(u,v,v′,w,w′,z), there is an isomorphism ULift_H(H₀(C_*(L;M))) ≅
ULift_H(N ⊗_U T) in ModuleCat_H(R). It sends the lifted class of the empty-exterior tensor 1 ⊗
m to up([m,up(1)]). The construction first transports homology to the lifted coefficient
complex, then identifies its H₀ with the augmentation tensor, and finally removes the
coefficient lift while lifting the output. -/
def rawCoefficientHomologyZeroTensorIsoAt :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology 0) ≅
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
      (envelopingTrivialObject R L)) :=
  rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0 ≪≫
    nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) ≪≫
      (rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M).toModuleIso

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. If U = U_R(L), N is the
right representation with m·ι(x) = −[x,m], and T is the augmentation left U-module, then
H₀(C_*(L;M)) ≃ₗ[R] N ⊗_U T. This equivalence uses the unlifted homology and balanced-quotient
carriers, with no equality required between their universes. It maps the class of 1 ⊗ m, with
1 ∈ Λ⁰_R L the empty exterior product, to [m,up(1)]. No freeness assumption on L is required. -/
def rawCoefficientHomologyZeroTensorEquivAt : (coefficientComplex R L M).homology 0 ≃ₗ[R]
  ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
  (envelopingTrivialObject R L)) :=
  (coefficientHomologyCarrierLiftEquiv.{u, v, w, max u v v' w w' z} R L M 0).trans
    ((rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).toLinearEquiv.trans
      (ULift.moduleEquiv : ULift.{max u v v' w w' z}
        ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L)) ≃ₗ[R]
        ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L))))

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Write cl_M(m) for the H₀
class of the empty-exterior tensor 1 ⊗ m. With U = U_R(L), N the right enveloping
representation of M, T the augmentation module, and H = max(u,v,v′,w,w′,z), the isomorphism
ULift_H(H₀(C_*(L;M))) ≅ ULift_H(N ⊗_U T) satisfies up(cl_M(m)) ↦ up([m,up(1)]). The
coefficient representative remains m and the augmentation representative is the scalar unit of
R. -/
theorem rawCoefficientHomologyZeroTensorIsoAt_class (m : M) :
    (rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom
      (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))) =
      ULift.up (TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          m (ULift.up (1 : R))) := by
  change rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M
    ((nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).hom
      ((rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom
        (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))))) = _
  rw [rawCoefficientHomologyTransportAt_zero_class, nativeCoefficientHomologyZeroTensorIso_class,
    rawCoefficientTrivialTensorOutputLiftEquiv_mk_up]

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Let N be its right
U_R(L)-representation and T the augmentation module with scalar carrier ULift(R). The R-linear
equivalence H₀(C_*(L;M)) ≃ₗ[R] N ⊗_{U_R(L)} T sends cl_M(m), the class of 1 ⊗ m in degree
zero, to [m,up(1)]. Here 1 is the empty exterior product, and the balanced class is formed
using the right enveloping action m·ι(x) = −[x,m]. -/
theorem rawCoefficientHomologyZeroTensorEquivAt_class (m : M) :
    rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M
      ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) =
      TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          m (ULift.up (1 : R)) := by
  change ((rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom
    (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
      ((coefficientComplex R L M).pOpcycles 0
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))))).down = _
  rw [rawCoefficientHomologyZeroTensorIsoAt_class]

local instance rawCoefficientZeroTensor_additive {A : Type a} [Ring A] [Algebra R A]
    (N : ModuleCat.{b} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, a, b, c} R A N).Additive :=
  ModuleCat.BalancedTensor.additive R A N

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put H =
max(u,v,v′,w,w′,z), U = U_R(L), and F_H(X) = N_H ⊗_U X for the right enveloping representation
N_H of the lifted coefficient. Let Φ_H : ULift_H(H₀(C_*(L;M))) ≅ (L₀F_H)(T_H) be the
homology-to-Tor comparison. Composing Φ_H.hom with F_H.fromLeftDerivedZero at the lifted
augmentation module T_H, the trivial-input lift cancellation, and the coefficient-to-output
lift equivalence gives exactly the map ULift_H(H₀(C_*(L;M))) → ULift_H(N ⊗_U T) that sends
up(cl_M(m)) to up([m,up(1)]). -/
theorem rawCoefficientHomologyIsoTorAt_zero_original [Module.Free R L] :
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom ≫
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R).fromLeftDerivedZero.app
        (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≫
        (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))).toModuleIso.hom ≫
          (rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M).toModuleIso.hom =
      (rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom := by
  let q := (rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M).toModuleIso.hom
  have h := rawCoefficientHomologyIsoTorAt_zero_canonical.{u, v, v', w, w', z} R L M
  have hOut : (rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom =
      (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom ≫
        (nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).hom ≫ q := rfl
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ q) h).trans hOut.symm)

/-- Let R be a commutative ring, L a free R-Lie module, and M an L-module. Put U = U_R(L), H =
max(u,v,v′,w,w′,z), and F_H(X) = N_H ⊗_U X, where N_H represents the lifted coefficient and
T_H is the lifted augmentation module. For a ∈ H₀(C_*(L;M)), apply the R-linear
homology-to-Tor equivalence at H, then the map (L₀F_H)(T_H) → F_H(T_H), then cancel the
trivial-input lift and the coefficient lift. The resulting element of N ⊗_U T equals the
canonical degree-zero tensor equivalence applied to a. Thus the equality holds on the unlifted
homology and tensor carriers, without an outer output lift. -/
theorem rawCoefficientHomologyEquivTorAt_zero_original [Module.Free R L]
    (a : (coefficientComplex R L M).homology 0) :
    rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).fromLeftDerivedZero.app
          (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L)).hom
          (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M 0 a))) =
    rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M a := by
  have h := congrArg (fun f => f.hom (ULift.up a))
    (rawCoefficientHomologyIsoTorAt_zero_original.{u, v, v', w, w', z} R L M)
  have hDown := congrArg
    (fun b : ULift.{max u v v' w w' z}
    ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
    (envelopingTrivialObject R L)) => b.down) h
  change rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).fromLeftDerivedZero.app
          (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L)).hom
          ((rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom (ULift.up a)))) =
    rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M a at hDown
  simpa only [rawCoefficientHomologyEquivTorAt_apply] using hDown

end ChevalleyEilenberg
