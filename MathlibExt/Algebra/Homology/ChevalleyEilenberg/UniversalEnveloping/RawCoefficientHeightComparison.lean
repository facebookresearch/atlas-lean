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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientTensorHeight

/-!
# Chevalley–Eilenberg homology under coefficient universe lifting

Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put H = max(u,v,v′,w,w′,z)
and H′ = max(H,t), where R, L, and M have carrier universes u, v, and w. Write M_H and M_H′
for the coefficient lifts, C_H and C_H′ for their Chevalley–Eilenberg complexes, and V for the
R-module lift from H to H′.

Flattening coefficients gives C_H′ ≅ V(C_H). In degree n this sends a ⊗ m to up(a ⊗ θ(m)),
where θ : M_H′ ≃ₗ[R] M_H preserves the underlying element of M. The chain isomorphism induces
H_n(C_H′) ≅ V(H_n(C_H)) and commutes with transport from H_n(C(M)). These statements require
no freeness of L.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z t a b c

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex coefficientComplexULift
  rawLieCoefficientLiftAt

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (M : LieModuleCat.{w} R L)


local instance rawCoefficientHeight_output_preservesHomology {A : Type a} [Ring A] :
    (ModuleCat.uliftFunctor.{c, b} A).PreservesHomology := Functor.preservesHomologyOfExact _

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put H = max(u,v,v′,w,w′,z)
and H′ = max(H,t), with R, L, and M in universes u, v, and w. For n ∈ ℕ, flattening the
coefficient lift defines Λⁿ_R L ⊗_R M_H′ ≃ₗ[R] ULift_{H′}(Λⁿ_R L ⊗_R M_H). The map is a ⊗ m ↦
up(a ⊗ θ(m)), where θ : M_H′ ≃ₗ[R] M_H is the coefficient equivalence induced by down and up
on M. -/
def rawCoefficientComplexHeightDegreeEquiv (n : ℕ) :
    (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)).X n ≃ₗ[R]
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).obj
      ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).X n) :=
  ((LieModuleCat.CoefficientULift.heightLinearEquiv.{u, v, w, max u v v' w w' z, t} R L M).lTensor
    (⋀[R]^n L)).trans
      (ULift.moduleEquiv : ULift.{max u v v' w w' z t}
        ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).X n) ≃ₗ[R]
        (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).X n).symm

theorem rawCoefficientComplexHeightDegreeEquiv_tmul (n : ℕ) (a : ⋀[R]^n L)
  (m : (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) :
    rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n (a ⊗ₜ[R] m) =
      ULift.up (a ⊗ₜ[R]
        LieModuleCat.CoefficientULift.heightLinearEquiv.{u, v, w, max u v v' w w' z, t} R L M m) := by
  let M₀ := rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M
  let h := LieModuleCat.CoefficientULift.heightLinearEquiv.{u, v, w, max u v v' w w' z, t} R L M
  exact congrArg (fun p : (coefficientComplex R L M₀).X n => ULift.up p)
    (LinearEquiv.lTensor_tmul (⋀[R]^n L) h a m)

theorem rawCoefficientComplexHeightDegreeEquiv_tmul_up (n : ℕ) (a : ⋀[R]^n L) (m : M) :
    rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n
      (a ⊗ₜ[R] (ULift.up m : (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M))) = ULift.up
        (a ⊗ₜ[R] (ULift.up m : (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))) := by
  exact rawCoefficientComplexHeightDegreeEquiv_tmul.{u, v, v', w, w', z, t} R L M n a (ULift.up m)

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put H = max(u,v,v′,w,w′,z)
and H′ = max(H,t). Write C_H = C_*(L;M_H), C_H′ = C_*(L;M_H′), and V for the R-module universe
lift H → H′. The degreewise maps a ⊗ m ↦ up(a ⊗ θ(m)), with θ : M_H′ ≃ₗ[R] M_H the coefficient
flattening, define a chain isomorphism C_H′ ≅ V(C_H) for the shape down ℕ. Thus they commute
with every coefficient differential C_{n+1} → C_n, including both the Lie-bracket and
coefficient-action terms. -/
def rawCoefficientComplexHeightIso :
    (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)) ≅
      ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n).toModuleIso)
    (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      let M₀ := LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M
      let M₁ := LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z t} R L M
      let h := LieModuleCat.CoefficientULift.heightDown.{u, v, w, max u v v' w w' z, t} R L M
      have hEquiv : (LieModuleCat.CoefficientULift.heightLinearEquiv.{u, v, w,
          max u v v' w w' z, t} R L M).toLinearMap = h.toLinearMap := by
        apply LinearMap.ext
        intro m
        rfl
      have hDegree (n : ℕ) (q : (coefficientComplex R L M₁).X n) :
          rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n q =
            ULift.up (h.toLinearMap.lTensor (⋀[R]^n L) q) := by
        induction q using TensorProduct.inductionOn with
        | add q r hq hr =>
            exact ((rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n).map_add q r).trans
              ((congrArg₂ (fun x y => x + y) hq hr).trans
                (congrArg ULift.up ((h.toLinearMap.lTensor (⋀[R]^n L)).map_add q r)).symm)
        | tmul a m =>
            have hm : (LieModuleCat.CoefficientULift.heightLinearEquiv.{u, v, w,
                max u v v' w w' z, t} R L M) m = h m :=
              LinearMap.congr_fun hEquiv m
            exact (rawCoefficientComplexHeightDegreeEquiv_tmul.{u, v, v', w, w', z, t} R L M n a m).trans
              ((congrArg (fun m : M₀ => ULift.up (a ⊗ₜ[R] m)) hm).trans
                (congrArg ULift.up (LinearMap.lTensor_tmul (⋀[R]^n L) h.toLinearMap a m)).symm)
      have hNat := LinearMap.congr_fun
        (coefficientDifferential_naturality.{u, v, max u v v' w w' z t, max u v v' w w' z}
          R L M₁ h j) p
      simp only [LinearMap.comp_apply] at hNat
      have hSource := hDegree (j + 1) p
      have hTarget := hDegree j (coefficientDifferential R L M₁ j p)
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      refine (congrArg ((((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (coefficientComplex R L M₀)).d (j + 1) j).hom hSource).trans ?_
      dsimp only [rawTensorHeightOutputLift]
      dsimp only [Functor.mapHomologicalComplex]
      simp only [coefficientComplex_d_succ, ModuleCat.uliftFunctor_map]
      change ULift.up (coefficientDifferential R L M₀ j
          (h.toLinearMap.lTensor (⋀[R]^(j + 1) L) p)) =
        rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M j
          (coefficientDifferential R L M₁ j p)
      exact (congrArg ULift.up hNat.symm).trans hTarget.symm)
/-- For a commutative ring R, an R-Lie algebra L, and an L-module M, put H = max(u,v,v′,w,w′,z)
and H′ = max(H,t). Let C_H and C_H′ be the Chevalley–Eilenberg complexes with the
corresponding coefficient lifts, and V the R-module lift H → H′. For every n ∈ ℕ there is an
isomorphism H_n(C_H′) ≅ V(H_n(C_H)). It is the homology map of the coefficient chain
isomorphism C_H′ ≅ V(C_H), followed by the comparison H_n(V(C_H)) ≅ V(H_n(C_H)) for the exact
functor V. -/
def rawCoefficientLiftHomologyHeightIso (n : ℕ) :
  (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', max z t} R L M)).homology n ≅
  (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).obj
  ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w w' z t} R)
    (ComplexShape.down ℕ) n).mapIso
      (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M) ≪≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
          (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)).app
          (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module, with carrier universes u,
v, and w. Put H = max(u,v,v′,w,w′,z) and H′ = max(H,t), and let V be the R-module lift H → H′.
For every n ∈ ℕ, the repeated lift V(ULift_H(H_n(C_*(L;M)))) is isomorphic to
ULift_H′(H_n(C_*(L;M))). The forward map sends up(up(a)) to up(a), and its inverse sends up(a)
to up(up(a)). -/
def rawOriginalCoefficientHomologyHeightIso (n : ℕ) :
    (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).obj
      ((ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n)) ≅
    (ModuleCat.uliftFunctor.{max u v v' w w' z t, max u v w} R).obj
      ((coefficientComplex R L M).homology n) :=
  (ModuleCat.uliftFunctorCompIso.{max u v v' w w' z, max u v v' w w' z t, max u v w} R).app
    ((coefficientComplex R L M).homology n)

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and C = C_*(L;M). Let E_H : ULift_H(C) ≅ C_*(L;M_H) and
E_H′ : ULift_H′(C) ≅ C_*(L;M_H′) be the coefficient lift comparisons. Let χ : V(ULift_H(C)) ≅
ULift_H′(C) flatten the repeated whole-complex lift, and k : C_*(L;M_H′) ≅ V(C_*(L;M_H))
flatten the coefficient lift. Then E_H′.hom ≫ k.hom = χ.inv ≫ V(E_H.hom). Both sides send up(a
⊗ m) to up(a ⊗ up(m)) in the degreewise exterior-first tensor order. -/
theorem rawCoefficientULiftComplexIso_height :
    (coefficientULiftComplexIso.{u, v, w, max u v v' w w' z t} R L M).hom ≫
      (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M).hom =
    (coefficientComplexULiftFlattenIso.{u, v, w, max u v v' w w' z,
      max u v v' w w' z t} R L M).inv ≫
        ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  let A := (((coefficientULiftComplexIso.{u, v, w, max u v v' w w' z t} R L M).hom ≫
    (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M).hom).f n).hom
  let B := (((coefficientComplexULiftFlattenIso.{u, v, w, max u v v' w w' z,
    max u v v' w w' z t} R L M).inv ≫
      ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M).hom).f n).hom
  change A p = B p
  cases p with
  | up p =>
      induction p using TensorProduct.inductionOn with
      | add p q hp hq =>
          change A (ULift.up p + ULift.up q) = B (ULift.up p + ULift.up q)
          exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hp hq).trans
            (B.map_add _ _).symm)
      | tmul a m =>
          have hHigh := coefficientULiftDegreeEquiv_up_tmul.{u, v, w, max u v v' w w' z t} R L M n a m
          have hLow := coefficientULiftDegreeEquiv_up_tmul.{u, v, w, max u v v' w w' z} R L M n a m
          have hHeight := rawCoefficientComplexHeightDegreeEquiv_tmul_up.{u, v, v', w, w', z, t}
            R L M n a m
          change rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n
            (coefficientULiftDegreeEquiv.{u, v, w, max u v v' w w' z t} R L M n
              (ULift.up (a ⊗ₜ[R] m))) =
            ULift.up (coefficientULiftDegreeEquiv.{u, v, w, max u v v' w w' z} R L M n
              (ULift.up (a ⊗ₜ[R] m)))
          exact (congrArg (rawCoefficientComplexHeightDegreeEquiv.{u, v, v', w, w', z, t} R L M n)
            hHigh).trans (hHeight.trans (congrArg ULift.up hLow).symm)

/-- Let R be a commutative ring, L an R-Lie algebra, and M an L-module. Put H =
max(u,v,v′,w,w′,z), H′ = max(H,t), and V = ULift_{H→H′}. For n ∈ ℕ, let T_H :
ULift_H(H_n(C_*(L;M))) ≅ H_n(C_*(L;M_H)) and T_H′ be the coefficient homology transports. Let
e : H_n(C_*(L;M_H′)) ≅ V(H_n(C_*(L;M_H))) be the induced height comparison, and b :
V(ULift_H(H_n(C_*(L;M)))) ≅ ULift_H′(H_n(C_*(L;M))) the repeated-lift flattening. Then
T_H′.hom ≫ e.hom = b.inv ≫ V(T_H.hom). -/
theorem rawCoefficientHomologyTransportAt_height (n : ℕ) :
    (rawCoefficientHomologyTransportAt.{u, v, v', w, w', max z t} R L M n).hom ≫
      (rawCoefficientLiftHomologyHeightIso.{u, v, v', w, w', z, t} R L M n).hom =
    (rawOriginalCoefficientHomologyHeightIso.{u, v, v', w, w', z, t} R L M n).inv ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M n).hom := by
  let K := coefficientComplex R L M
  let Q := coefficientComplexULift.{u, v, w, max u v v' w w' z} R L M
  let P := coefficientComplexULift.{u, v, w, max u v v' w w' z t} R L M
  let W₀ := ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R
  let W₁ := ModuleCat.uliftFunctor.{max u v v' w w' z t, max u v w} R
  letI : W₀.PreservesHomology := Functor.preservesHomologyOfExact W₀
  letI : W₁.PreservesHomology := Functor.preservesHomologyOfExact W₁
  let e := ModuleCat.uliftFunctorCompIso.{max u v v' w w' z, max u v v' w w' z t, max u v w} R
  let χ := coefficientComplexULiftFlattenIso.{u, v, w, max u v v' w w' z,
    max u v v' w w' z t} R L M
  let m₀ := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n W₀
  let m₁ := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n W₁
  let mV := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
    (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)
  let b := rawOriginalCoefficientHomologyHeightIso.{u, v, v', w, w', z, t} R L M n
  let E₀ := coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M
  let E₁ := coefficientULiftComplexIso.{u, v, w, max u v v' w w' z t} R L M
  have hχ :
    (Functor.mapHomologicalComplexCompIso (F := W₀) (G := (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R)) e
      (ComplexShape.down ℕ)).hom.app K = χ.hom := by
    apply HomologicalComplex.hom_ext
    intro j
    rfl
  have hComp : HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (m₀.hom.app K) ≫ e.hom.app (K.homology n) =
        m₁.hom.app K := by
    have h := HomologicalComplex.comparisonHom_comp (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R) W₀ W₁ e n
      P Q K
      χ.inv (𝟙 Q) (Iso.refl (P.homology n)) (Iso.refl (Q.homology n)) (Iso.refl (K.homology n))
    rw [hχ] at h
    let V := rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R
    have hiP : HomologicalComplex.homologyMap (𝟙 P) n = 𝟙 (P.homology n) :=
      (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) n).map_id P
    have hiQ : HomologicalComplex.homologyMap (𝟙 Q) n = 𝟙 (Q.homology n) :=
      (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) n).map_id Q
    have hLift : (V.mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 Q) = 𝟙 _ :=
      (V.mapHomologicalComplex (ComplexShape.down ℕ)).map_id Q
    have hIdentity : χ.inv ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 Q) ≫ χ.hom = 𝟙 P :=
      (congrArg (fun f => χ.inv ≫ f ≫ χ.hom) hLift).trans
        ((congrArg (fun f => χ.inv ≫ f) (Category.id_comp χ.hom)).trans χ.inv_hom_id)
    have hOut := V.map_id (Q.homology n)
    have hW₀ := W₀.map_id (K.homology n)
    have hW₁ := W₁.map_id (K.homology n)
    have hRight : HomologicalComplex.homologyMap
        (χ.inv ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 Q) ≫ χ.hom) n ≫
          m₁.hom.app K ≫ W₁.map (𝟙 (K.homology n)) = m₁.hom.app K := by
      exact (congrArg₂ (fun f g => f ≫ m₁.hom.app K ≫ g)
        ((congrArg (fun f => HomologicalComplex.homologyMap f n) hIdentity).trans hiP) hW₁).trans
          ((Category.id_comp _).trans (Category.comp_id _))
    have hInner : HomologicalComplex.homologyMap (𝟙 Q) n ≫ m₀.hom.app K ≫
        W₀.map (𝟙 (K.homology n)) = m₀.hom.app K :=
      (congrArg₂ (fun f g => f ≫ m₀.hom.app K ≫ g) hiQ hW₀).trans
        ((Category.id_comp _).trans (Category.comp_id _))
    have hLeft : HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q ≫
        V.map (𝟙 (Q.homology n)) ≫
          V.map (HomologicalComplex.homologyMap (𝟙 Q) n ≫ m₀.hom.app K ≫
            W₀.map (𝟙 (K.homology n))) ≫ e.hom.app (K.homology n) =
      HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q ≫
        V.map (m₀.hom.app K) ≫ e.hom.app (K.homology n) := by
      exact (congrArg₂ (fun f g => HomologicalComplex.homologyMap χ.inv n ≫
        mV.hom.app Q ≫ f ≫ g ≫ e.hom.app (K.homology n)) hOut (congrArg V.map hInner)).trans
          (congrArg (fun f => HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q ≫ f)
            (Category.id_comp _))
    exact hLeft.symm.trans (h.trans hRight)
  have hWhole : m₁.inv.app K ≫ HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q =
      b.inv ≫ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (m₀.inv.app K) := by
    let tail := (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (m₀.hom.app K) ≫ e.hom.app (K.homology n)
    apply (cancel_mono tail).1
    calc
      (m₁.inv.app K ≫ HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q) ≫ tail =
          m₁.inv.app K ≫
            (HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q ≫
              (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (m₀.hom.app K) ≫ e.hom.app (K.homology n)) := by
                simp only [tail, Category.assoc]
      _ = 𝟙 (W₁.obj (K.homology n)) := by rw [hComp]; exact m₁.inv_hom_id_app K
      _ = (b.inv ≫ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (m₀.inv.app K)) ≫ tail := by
        let V := rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R
        have hId := m₀.inv_hom_id_app K
        have hMapped : V.map (m₀.inv.app K) ≫ V.map (m₀.hom.app K) = 𝟙 _ :=
          (V.map_comp _ _).symm.trans ((congrArg V.map hId).trans (V.map_id _))
        have hb : e.hom.app (K.homology n) = b.hom := rfl
        have hTail : (b.inv ≫ V.map (m₀.inv.app K)) ≫ tail = 𝟙 _ := by
          dsimp only [tail]
          have hAssoc : (b.inv ≫ V.map (m₀.inv.app K)) ≫
              (V.map (m₀.hom.app K) ≫ e.hom.app (K.homology n)) =
            b.inv ≫ (V.map (m₀.inv.app K) ≫ V.map (m₀.hom.app K)) ≫
              e.hom.app (K.homology n) := by simp only [Category.assoc]
          exact hAssoc.trans
            ((congrArg (fun q => b.inv ≫ q ≫ e.hom.app (K.homology n)) hMapped).trans
              ((congrArg (fun q => b.inv ≫ q) (Category.id_comp _)).trans
                ((congrArg (fun q => b.inv ≫ q) hb).trans b.inv_hom_id)))
        exact hTail.symm
  have hVNat : HomologicalComplex.homologyMap
      (((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        E₀.hom) n ≫ mV.hom.app (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) =
      mV.hom.app Q ≫ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (HomologicalComplex.homologyMap E₀.hom n) :=
    mV.hom.naturality E₀.hom
  have hCE : E₁.hom ≫ (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M).hom =
      χ.inv ≫
        ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        E₀.hom :=
    rawCoefficientULiftComplexIso_height.{u, v, v', w, w', z, t} R L M
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' w w' z t} R)
    (ComplexShape.down ℕ) n
  let hHeight := (rawCoefficientComplexHeightIso.{u, v, v', w, w', z, t} R L M).hom
  let vE := ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).mapHomologicalComplex
    (ComplexShape.down ℕ)).map E₀.hom
  have hInputHigh : (rawCoefficientHomologyTransportAt.{u, v, v', w, w', max z t} R L M n).hom =
      m₁.inv.app K ≫ HomologicalComplex.homologyMap E₁.hom n := rfl
  have hInputLow : (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M n).hom =
      m₀.inv.app K ≫ HomologicalComplex.homologyMap E₀.hom n := rfl
  have hHeightHom : (rawCoefficientLiftHomologyHeightIso.{u, v, v', w, w', z, t} R L M n).hom =
      HomologicalComplex.homologyMap hHeight n ≫
        mV.hom.app (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) := rfl
  have hCEHom : HomologicalComplex.homologyMap E₁.hom n ≫ HomologicalComplex.homologyMap hHeight n =
      HomologicalComplex.homologyMap χ.inv n ≫ HomologicalComplex.homologyMap vE n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f n) hCE).trans
        (HomologicalComplex.homologyMap_comp _ _ n))
  have hCalc :
      (m₁.inv.app K ≫ HomologicalComplex.homologyMap E₁.hom n) ≫
        (HomologicalComplex.homologyMap hHeight n ≫
          mV.hom.app (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))) =
      b.inv ≫ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
        (m₀.inv.app K ≫ HomologicalComplex.homologyMap E₀.hom n) := by
    calc
      _ = m₁.inv.app K ≫ (HomologicalComplex.homologyMap E₁.hom n ≫
          HomologicalComplex.homologyMap hHeight n) ≫
            mV.hom.app (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) := by
          simp only [Category.assoc]
      _ = m₁.inv.app K ≫ HomologicalComplex.homologyMap χ.inv n ≫
          HomologicalComplex.homologyMap vE n ≫
            mV.hom.app (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
          congrArg (fun q => m₁.inv.app K ≫ q ≫ _) hCEHom
      _ = (m₁.inv.app K ≫ HomologicalComplex.homologyMap χ.inv n ≫ mV.hom.app Q) ≫
          (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
            (HomologicalComplex.homologyMap E₀.hom n) := by
          simpa only [vE, Category.assoc] using
            congrArg (fun q => m₁.inv.app K ≫ HomologicalComplex.homologyMap χ.inv n ≫ q) hVNat
      _ = (b.inv ≫ (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map (m₀.inv.app K)) ≫
          (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map
            (HomologicalComplex.homologyMap E₀.hom n) :=
          congrArg (fun q => q ≫ _) hWhole
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun q => b.inv ≫ q)
          ((rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map_comp _ _).symm)
  exact (congrArg₂ (fun f g => f ≫ g) hInputHigh hHeightHom).trans
    (hCalc.trans (congrArg (fun q => b.inv ≫
      (rawTensorHeightOutputLift.{u, v, v', w, w', z, t} R).map q) hInputLow.symm))

end ChevalleyEilenberg
