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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientULiftTransport
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.NativeCoefficients

/-!
# CE coefficient homology and Tor across separate carriers

For a Lie coefficient M in its own carrier universe, lift only the coefficient to a common
height H containing the scalar, Lie and both potential coefficient universes. The
coefficient-lift comparison identifies the lift of H_n(CE(L,M)) with H_n of CE for the lifted
coefficient.

Represent that lifted coefficient as a right enveloping module and take the left-derived
balanced tensor functor at the lifted trivial left module. When L is free, the CE/Tor
comparison gives both a categorical isomorphism on the lifted homology object and an R-linear
equivalence from the exact unlifted homology carrier.

Compatible Lie and coefficient maps define the CE and derived tensor maps independently. The
comparisons commute with both maps, and their degree-zero square retains the canonical
coefficient coinvariant and scalar-unit tensor map.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z a b

open CategoryTheory
open scoped ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). rawLieCoefficientLiftAt is M_H = CoefficientULift.obj M in
LieModuleCat.{H} R L, with the transported R and Lie actions. -/
def rawLieCoefficientLiftAt (M : LieModuleCat.{w} R L) : LieModuleCat.{max u v v' w w' z} R L :=
  LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). For n : ℕ, rawCoefficientHomologyTransportAt identifies
ULift_H(H_n(CE(L,M))) with H_n(CE(L,M_H)), by the coefficient-carrier lift comparison. -/
def rawCoefficientHomologyTransportAt (M : LieModuleCat.{w} R L) (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ≅
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology n :=
  coefficientHomologyCoefficientLiftIso.{u, v, w, max u v v' w w' z} R L M n

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). For n : ℕ, rawCoefficientHomologyTransportEquivAt is the R-linear
equivalence H_n(CE(L,M)) ≃ₗ[R] H_n(CE(L,M_H)), including its input/output up/down coordinates. -/
def rawCoefficientHomologyTransportEquivAt (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≃ₗ[R]
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology n :=
  coefficientHomologyCoefficientLiftEquiv.{u, v, w, max u v v' w w' z} R L M n

local instance rawCoefficientTensor_additive {A : Type v} [Ring A] [Algebra R A]
    (M : ModuleCat.{a} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, v, a, b} R A M).Additive :=
  ModuleCat.BalancedTensor.additive R A M

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). rawLieCoefficientTorAt M n is (F_H.leftDerived n).obj T_H in
ModuleCat.{H} R. The coefficient and trivial input are their explicit lifts. -/
def rawLieCoefficientTorAt (M : LieModuleCat.{w} R L) (n : ℕ) : (ModuleCat.{max u v v' w w' z} R) :=
  (((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :
        ModuleCat.{max u v v' w w' z} U ⥤ (ModuleCat.{max u v v' w w' z} R)).leftDerived n).obj
          (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L))

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). Assume Module.Free R L. For n : ℕ, rawCoefficientHomologyIsoTorAt
identifies the module lift of H_n(CE(L,M)) with rawLieCoefficientTorAt M n, by coefficient
homology transport followed by the represented-coefficient resolution comparison. -/
def rawCoefficientHomologyIsoTorAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ≅
      rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n :=
  rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M n ≪≫
    nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). Assume Module.Free R L. For n : ℕ, rawCoefficientTorIsoHomologyAt is the
inverse of rawCoefficientHomologyIsoTorAt, from Tor_H to the lift of H_n(CE(L,M)). -/
def rawCoefficientTorIsoHomologyAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n ≅
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
        ((coefficientComplex R L M).homology n) :=
  (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).symm

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). Assume Module.Free R L. For n : ℕ, rawCoefficientHomologyEquivTorAt maps
H_n(CE(L,M)) R-linearly to rawLieCoefficientTorAt M n by input up followed by the categorical
comparison. -/
def rawCoefficientHomologyEquivTorAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≃ₗ[R]
      rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n :=
  (coefficientHomologyCarrierLiftEquiv.{u, v, w, max u v v' w w' z} R L M n).trans
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).toLinearEquiv

@[simp]
theorem rawCoefficientHomologyEquivTorAt_apply [Module.Free R L]
    (M : LieModuleCat.{w} R L) (n : ℕ) (a : (coefficientComplex R L M).homology n) :
    rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n a =
      (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom (ULift.up a) := rfl

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). Assume Module.Free R L. For n : ℕ, rawCoefficientTorEquivHomologyAt is
the inverse R-linear equivalence from Tor_H to H_n(CE(L,M)). -/
def rawCoefficientTorEquivHomologyAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n ≃ₗ[R]
      (coefficientComplex R L M).homology n :=
  (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n).symm

/-- Let R : Type u be commutative, L : Type v an R-Lie algebra, M : LieModuleCat.{w} R L and H =
max u v v' w w' z. Let M_H be its coefficient-carrier lift, N_H its right
U_R(L)-representation and T_H the lifted trivial left enveloping module. Put F_H(X) =
Balanced(R,U,N_H,X). Assume Module.Free R L. Let Φ_H be the categorical CE/Tor comparison, d₀
= F_H.fromLeftDerivedZero at T_H, c_T the trivial-input lift cancellation and t_H the
coefficient homology transport. Then Φ_H,0.hom ≫ d₀ ≫ c_T equals t_H,0.hom followed by
nativeCoefficientHomologyZeroTensorIso for M_H. -/
theorem rawCoefficientHomologyIsoTorAt_zero_canonical [Module.Free R L]
    (M : LieModuleCat.{w} R L) :
    let M₁ := rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M
    let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L M₁
    let F := (ModuleCat.BalancedTensor.functor R U N₁ :
      ModuleCat.{max u v v' w w' z} U ⥤ (ModuleCat.{max u v v' w w' z} R))
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom ≫
      F.fromLeftDerivedZero.app (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≫
        (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L N₁).toModuleIso.hom =
      (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom ≫
        (nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L M₁).hom := by
  dsimp only
  let t := rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0
  let e := nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) 0
  have he : (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom =
      t.hom ≫ e.hom := rfl
  have h := nativeCoefficientHomologyIsoTor_zero_canonical.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  exact (congrArg (fun q => q ≫ _ ≫ _) he).trans
    ((Category.assoc _ _ _).trans (congrArg (fun q => t.hom ≫ q) h))

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{w} R L) (M' : LieModuleCat.{w'} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : M →ₗ⁅R,L⁆ f* M' with Lie carriers v,v' and
coefficient carriers w,w'. Use H = max u v v' w w' z and the represented right enveloping
coefficient modules of the two coefficient lifts. rawLieCoefficientMapAt sends ULift.up m to
ULift.up(h(m)) as a Lie-module map M_H → f* M'_H. -/
def rawLieCoefficientMapAt :
    rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M →ₗ⁅R,L⁆
      LieModuleCat.restrictObj f (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M') :=
  LieModuleCat.CoefficientULift.jointMap.{u, v, w, w', v', max u v v' w w' z} R L f M M' h

@[simp]
theorem rawLieCoefficientMapAt_up (m : M) :
    rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h (ULift.up m) = ULift.up (h m) := rfl

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : M →ₗ⁅R,L⁆ f* M' with Lie carriers v,v' and
coefficient carriers w,w'. Use H = max u v v' w w' z and the represented right enveloping
coefficient modules of the two coefficient lifts. For n : ℕ, rawCoefficientHomologyMapAt maps
the module lift of H_n(CE(L,M)) to that of H_n(CE(L',M')), using the CE chain map and
canonical homology-lift comparisons. -/
def rawCoefficientHomologyMapAt (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ⟶
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).obj
      ((coefficientComplex R L' M').homology n) :=
  coefficientRawHomologyMapAt.{u, v, w, z, v', w'} R L f M M' h n

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : M →ₗ⁅R,L⁆ f* M' with Lie carriers v,v' and
coefficient carriers w,w'. Use H = max u v v' w w' z and the represented right enveloping
coefficient modules of the two coefficient lifts. rawOriginalCoefficientHomologyMapAt is the
R-linear map H_n(CE(L,M)) → H_n(CE(L',M')) obtained by input up, rawCoefficientHomologyMapAt
and output down. -/
def rawOriginalCoefficientHomologyMapAt (n : ℕ) :
    (coefficientComplex R L M).homology n →ₗ[R] (coefficientComplex R L' M').homology n :=
  coefficientOriginalHomologyMapAt.{u, v, w, z, v', w'} R L f M M' h n

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : M →ₗ⁅R,L⁆ f* M' with Lie carriers v,v' and
coefficient carriers w,w'. Use H = max u v v' w w' z and the represented right enveloping
coefficient modules of the two coefficient lifts. For n : ℕ, rawLieCoefficientTorMapAt maps
the two Tor_H objects via the right coefficient representations and canonical UEA.map f
scalar-change square. -/
def rawLieCoefficientTorMapAt (n : ℕ) :
    rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n ⟶
      rawLieCoefficientTorAt.{u, v', v, w', w, z} R L' M' n :=
  nativeLieCoefficientTorMap.{u, v, v', max w w' z} R L f
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
    (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')
    (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h) n

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : M →ₗ⁅R,L⁆ f* M' with Lie carriers v,v' and
coefficient carriers w,w'. Use H = max u v v' w w' z and the represented right enveloping
coefficient modules of the two coefficient lifts. If L and L' are free over R, the lifted CE
homology map followed by the target CE/Tor comparison equals the source comparison followed by
rawLieCoefficientTorMapAt in every degree. -/
theorem rawCoefficientHomologyIsoTorAt_naturality [Module.Free R L] [Module.Free R L'] (n : ℕ) :
    rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n ≫
      (rawCoefficientHomologyIsoTorAt.{u, v', v, w', w, z} R L' M' n).hom =
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom ≫
      rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n := by
  let A := coefficientHomologyULiftIso.{u, v, w, max u v v' w w' z} R L M n
  let A' := coefficientHomologyULiftIso.{u, v', w', max u v v' w w' z} R L' M' n
  let e := coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M
  let e' := coefficientULiftComplexIso.{u, v', w', max u v v' w w' z} R L' M'
  let a := coefficientLieComplexMapULiftAt.{u, v, w, z, v', w'} R L f M M' h
  let b := nativeCoefficientLieComplexMap.{u, v, v', max w w' z} R L f
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
    (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M') (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h)
  have hC : a ≫ e'.hom = e.hom ≫ b :=
    coefficientULiftComplexIso_joint_naturality.{u, v, w, z, v', w'} R L f M M' h
  have hH : HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap e'.hom n =
      HomologicalComplex.homologyMap e.hom n ≫ HomologicalComplex.homologyMap b n := by
    exact (HomologicalComplex.homologyMap_comp a e'.hom n).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f n) hC).trans
        (HomologicalComplex.homologyMap_comp e.hom b n))
  let T := nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n
  let T' := nativeCoefficientHomologyIsoTor.{u, v', v, max w w' z} R L'
    (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M') n
  have hSource : (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom =
      A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫ T.hom := rfl
  have hTarget : (rawCoefficientHomologyIsoTorAt.{u, v', v, w', w, z} R L' M' n).hom =
      A'.hom ≫ HomologicalComplex.homologyMap e'.hom n ≫ T'.hom := rfl
  have hMap : rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n =
      A.hom ≫ HomologicalComplex.homologyMap a n ≫ A'.inv := rfl
  have hNat : HomologicalComplex.homologyMap b n ≫ T'.hom =
      T.hom ≫ rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n :=
    nativeCoefficientHomologyIsoTor_lie_naturality.{u, v, v', max w w' z} R L f
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
      (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')
      (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h) n
  have cancel {W X Y Z V : ModuleCat.{max u v v' w w' z} R}
      (f : W ⟶ X) (g : X ⟶ Y) (e : Z ≅ Y) (h : Y ⟶ V) :
      (f ≫ g ≫ e.inv) ≫ (e.hom ≫ h) = f ≫ g ≫ h := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hCalc :
      (A.hom ≫ HomologicalComplex.homologyMap a n ≫ A'.inv) ≫
          (A'.hom ≫ HomologicalComplex.homologyMap e'.hom n ≫ T'.hom) =
        (A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫ T.hom) ≫
          rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n := by
    calc
      _ = A.hom ≫ HomologicalComplex.homologyMap a n ≫
          HomologicalComplex.homologyMap e'.hom n ≫ T'.hom := cancel _ _ _ _
      _ = A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫
          HomologicalComplex.homologyMap b n ≫ T'.hom := by
        exact congrArg (fun q => A.hom ≫ q ≫ T'.hom) hH
      _ = _ := by
        exact (congrArg (fun q => A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫ q) hNat).trans
          (Category.assoc _ _ _).symm
  exact (congrArg₂ (fun f g => f ≫ g) hMap hTarget).trans
    (hCalc.trans (congrArg (fun q => q ≫
      rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n) hSource).symm)

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : M →ₗ⁅R,L⁆ f* M' with Lie carriers v,v' and
coefficient carriers w,w'. Use H = max u v v' w w' z and the represented right enveloping
coefficient modules of the two coefficient lifts. If L and L' are free, Φ_target ∘
rawOriginalCoefficientHomologyMapAt = rawLieCoefficientTorMapAt ∘ Φ_source as R-linear maps on
the unlifted homology carriers, where Φ is rawCoefficientHomologyEquivTorAt. -/
theorem rawCoefficientHomologyEquivTorAt_naturality [Module.Free R L] [Module.Free R L'] (n : ℕ) :
    (rawCoefficientHomologyEquivTorAt.{u, v', v, w', w, z} R L' M' n).toLinearMap.comp
      (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom.comp
      (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n).toLinearMap := by
  ext a
  have hNat := congrArg
    (fun f => f.hom (ULift.up a)) (rawCoefficientHomologyIsoTorAt_naturality.{u, v, v', w, w', z} R L f M M' h n)
  change (rawCoefficientHomologyIsoTorAt.{u, v', v, w', w, z} R L' M' n).hom
      ((rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a)) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom
      ((rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom (ULift.up a)) at hNat
  have hUp : (ULift.up (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n a) :
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).obj
        ((coefficientComplex R L' M').homology n)) =
      (rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a) := by
    change ULift.up (((rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a)).down) = _
    cases ((rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a))
    rfl
  change rawCoefficientHomologyEquivTorAt.{u, v', v, w', w, z} R L' M' n
      (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n a) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom
      (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n a)
  rw [rawCoefficientHomologyEquivTorAt_apply, rawCoefficientHomologyEquivTorAt_apply, hUp]
  exact hNat

end JointMaps

end ChevalleyEilenberg
