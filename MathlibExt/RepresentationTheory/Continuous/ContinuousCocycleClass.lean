/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Continuous degree-one cocycle class from an inhomogeneous cocycle

For a `TopRep k G` and a function `c : G → X` satisfying the additive
inhomogeneous equation `c (g * h) = X.ρ g (c h) + c g`, this file builds the
homogeneous degree-one cochain with values `Ψ x y = X.ρ x (c (x⁻¹ * y))`.

Main constructions:
* `homOneCochain`: the invariant homogeneous degree-one cochain in
  `TopRep.homogeneousCochains`.
* `homOneCochain_val_apply`: transparent computation of its values.
* `homOneCochain_mem_ker`: it lies in the kernel of the degree-one differential,
  using the cocycle equation.
* `oneCocycleMor`: the packaged cycle in `ContinuousCohomology.cocycles`
  via `HomologicalComplex.liftCycles`.
* `oneCohomClassMor`: its image under `ContinuousCohomology.π` in
  `continuousCohomology`.

Orientation: inhomogeneous `c (g * h) = X.ρ g (c h) + c g`; homogeneous
`Ψ x y = X.ρ x (c (x⁻¹ * y))` with diagonal invariance
`Ψ (g * x) (g * y) = X.ρ g (Ψ x y)` and kernel identity
`Ψ y z - Ψ x z + Ψ x y = 0`.

Continuity is taken as an explicit hypothesis on the uncurried map
`(x, y) ↦ X.ρ x (c (x⁻¹ * y))`; continuity of `c` alone is not used.
Currying happens only after that hypothesis is supplied.

Nonclaims: no identification of ordinary, continuous, or étale degree-one
objects; no finite-quotient comparison; no Kummer isomorphism; no motivic
comparison; no higher-weight statement.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousAdd k] [ContinuousSMul k k]

namespace ContinuousCohomology

/-- Homogeneous degree-one cochain from an inhomogeneous cocycle.

Given `c` with `c (g * h) = X.ρ g (c h) + c g` and continuity of the uncurried
`Ψ`, this packages `Ψ x y = X.ρ x (c (x⁻¹ * y))` as an invariant element of
`TopRep.homogeneousCochains`. Reuses `TopRep.homogeneousCochains` and
`ContRepresentation.coind₁_apply_apply` for the invariance computation. -/
noncomputable def homOneCochain (X : TopRep k G) (c : G → X)
    (hcont : Continuous (fun p : G × G => X.ρ p.1 (c (p.1⁻¹ * p.2)))) :
    (TopRep.homogeneousCochains X).X 1 :=
  ⟨(⟨_, hcont⟩ : C(G × G, X)).curry, by
    intro g
    ext x y
    change X.ρ g (((⟨_, hcont⟩ : C(G × G, X)).curry) (g⁻¹ * x) (g⁻¹ * y)) =
      ((⟨_, hcont⟩ : C(G × G, X)).curry) x y
    simp only [ContinuousMap.curry_apply]
    have hρmul : ∀ a b (v : X), X.ρ (a * b) v = X.ρ a (X.ρ b v) := by
      intro a b v
      have h := map_mul X.ρ a b
      have h2 := DFunLike.congr_fun h v
      simp
    have hgx : g * (g⁻¹ * x) = x := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hxy : (g⁻¹ * x)⁻¹ * (g⁻¹ * y) = x⁻¹ * y := by
      rw [mul_inv_rev, mul_assoc, inv_inv, mul_inv_cancel_left]
    calc X.ρ g (X.ρ (g⁻¹ * x) (c ((g⁻¹ * x)⁻¹ * (g⁻¹ * y))))
        = X.ρ g (X.ρ (g⁻¹ * x) (c (x⁻¹ * y))) := by rw [hxy]
      _ = X.ρ (g * (g⁻¹ * x)) (c (x⁻¹ * y)) := by rw [← hρmul]
      _ = X.ρ x (c (x⁻¹ * y)) := by rw [hgx]⟩

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- Transparent values of `homOneCochain`. Needed downstream for kernel and
comparison arguments. -/
@[simp]
theorem homOneCochain_val_apply (X : TopRep k G) (c : G → X)
    (hcont : Continuous (fun p : G × G => X.ρ p.1 (c (p.1⁻¹ * p.2))))
    (x y : G) :
    (homOneCochain X c hcont).val x y = X.ρ x (c (x⁻¹ * y)) :=
  rfl

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- The homogeneous cochain lies in the kernel of the degree-one differential.

Uses `TopRep.homogeneousCochains.d_apply`, `TopRep.hom_d_succ`,
`TopRep.hom_ofHom`, `TopRep.d_zero`,
`ContRepresentation.coind₁ι_toFun`, `ContRepresentation.coind₁Map_toFun`, and
pointwise continuous-map lemmas, plus the cocycle equation.

The proof first reduces to the subtype kernel membership, derives the pointwise
cocycle identity `hF`, unfolds the homogeneous differential at `.hom`, applies
three-argument function extensionality, and only then evaluates the coinduction
terms pointwise so the pointwise identity closes the goal. -/
theorem homOneCochain_mem_ker (X : TopRep k G) (c : G → X)
    (hcocycle : ∀ g h : G, c (g * h) = X.ρ g (c h) + c g)
    (hcont : Continuous (fun p : G × G => X.ρ p.1 (c (p.1⁻¹ * p.2)))) :
    ((TopRep.homogeneousCochains X).d 1 2).hom
      (homOneCochain X c hcont) = 0 := by
  have hker : homOneCochain X c hcont ∈ ((TopRep.homogeneousCochains X).d 1 2).hom.ker := by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    apply Subtype.ext
    have hρmul : ∀ a b (v : X), X.ρ (a * b) v = X.ρ a (X.ρ b v) := by
      intro a b v; have h := map_mul X.ρ a b
      have h2 := DFunLike.congr_fun h v; simp
    have hF : ∀ x y z : G, (homOneCochain X c hcont).val y z -
        (homOneCochain X c hcont).val x z +
        (homOneCochain X c hcont).val x y = 0 := by
      intro x y z
      have hxyz : (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z := by
        rw [mul_assoc, ← mul_assoc y y⁻¹ z, mul_inv_cancel, one_mul]
      have hx : x * (x⁻¹ * y) = y := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      have hc : c (x⁻¹ * z) = X.ρ (x⁻¹ * y) (c (y⁻¹ * z)) + c (x⁻¹ * y) := by
        rw [← hxyz]; exact hcocycle (x⁻¹ * y) (y⁻¹ * z)
      rw [homOneCochain_val_apply, homOneCochain_val_apply, homOneCochain_val_apply,
        hc, map_add, ← hρmul, hx]; abel
    simp only [TopRep.homogeneousCochains.d_apply] at ⊢
    simp only [TopRep.hom_d_succ, TopRep.hom_ofHom, TopRep.d_zero,
      ContIntertwiningMap.sub_apply,
      ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
      ] at ⊢
    ext x y z
    simp only [ContinuousMap.sub_apply,
      ContinuousMap.const_apply, ContinuousMap.comp_apply,
      ] at ⊢
    let hFx : C(G, X) := (homOneCochain X c hcont).val x
    have hRem : ((X.ρ.coind₁ι (hFx y)) z) = hFx y := by
      simp only [ContRepresentation.coind₁ι_toFun, ContinuousMap.const_apply]
    have hInnerDirect : ((((X.resolutionX 0).ρ.coind₁.coind₁ι -
        ContRepresentation.coind₁Map X.ρ.coind₁ι) hFx) y) z =
        hFx z - hFx y := by
      simp only [ContIntertwiningMap.sub_apply, ContRepresentation.coind₁ι_toFun,
        ContRepresentation.coind₁Map_toFun, ContinuousMap.const_apply,
        ContinuousMap.comp_apply, ContinuousMap.sub_apply]
      change hFx z - ((X.ρ.coind₁ι (hFx y)) z) = hFx z - hFx y
      rw [hRem]
    change (homOneCochain X c hcont).val y z -
      ((((X.resolutionX 0).ρ.coind₁.coind₁ι -
        ContRepresentation.coind₁Map X.ρ.coind₁ι) hFx) y) z = 0
    rw [hInnerDirect, sub_sub_eq_add_sub]
    change (homOneCochain X c hcont).val y z + hFx y - hFx z = 0
    have h := hF x y z
    change (homOneCochain X c hcont).val y z +
      (homOneCochain X c hcont).val x y -
      (homOneCochain X c hcont).val x z = 0
    have hEq : (homOneCochain X c hcont).val y z +
        (homOneCochain X c hcont).val x y -
        (homOneCochain X c hcont).val x z =
        (homOneCochain X c hcont).val y z -
        (homOneCochain X c hcont).val x z +
        (homOneCochain X c hcont).val x y := by abel
    rw [hEq]
    exact h
  exact LinearMap.mem_ker.mp hker

/-- Universe-raised scalar down-map reusing `ContinuousLinearEquiv.ulift`. -/
noncomputable def uliftDown : ULift.{w, u} k →L[k] k :=
  (ContinuousLinearEquiv.ulift).toContinuousLinearMap

-- File-local named instance reusing the pinned transfer lemma, registered locally
-- so it reaches TC search at the `TopModuleCat.of/ofHom` sites below.
local instance uliftContinuousSMul : ContinuousSMul k (ULift.{w, u} k) :=
  ContinuousLinearEquiv.ulift.continuousSMul

/-- Packaged degree-one cycle via `HomologicalComplex.liftCycles`. -/
noncomputable def oneCocycleMor (X : TopRep.{max v (max u w), u, v} k G) (c : G → X)
    (hcocycle : ∀ g h : G, c (g * h) = X.ρ g (c h) + c g)
    (hcont : Continuous (fun p : G × G => X.ρ p.1 (c (p.1⁻¹ * p.2)))) :
    TopModuleCat.of k (ULift.{max v (max u w), u} k) ⟶
      ContinuousCohomology.cocycles.{u, v, max u w} X 1 :=
  (TopRep.homogeneousCochains.{u, v, max u w} X).liftCycles
    (TopModuleCat.ofHom
      ((ContinuousLinearMap.toSpanSingleton k (homOneCochain.{u, v, max u w} X c hcont)).comp
        uliftDown.{u, max v (max u w)}))
    2 (by simp) (by
      ext r
      simp only [
        ]
      change ((TopRep.homogeneousCochains.{u, v, max u w} X).d 1 2).hom
        (r.down • homOneCochain.{u, v, max u w} X c hcont) = 0
      rw [map_smul, homOneCochain_mem_ker.{u, v, max u w} X c hcocycle hcont, smul_zero])

/-- Resulting continuous cohomology class via `ContinuousCohomology.π`. -/
noncomputable def oneCohomClassMor (X : TopRep.{max v (max u w), u, v} k G) (c : G → X)
    (hcocycle : ∀ g h : G, c (g * h) = X.ρ g (c h) + c g)
    (hcont : Continuous (fun p : G × G => X.ρ p.1 (c (p.1⁻¹ * p.2)))) :
    TopModuleCat.of k (ULift.{max v (max u w), u} k) ⟶ continuousCohomology.{u, v, max u w} 1 X :=
  oneCocycleMor X c hcocycle hcont ≫ ContinuousCohomology.π.{u, v, max u w} X 1

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- Generic degree-one boundary equality corollary for continuous cohomology.

If two degree-one cycles differ by a boundary, `z₁ - z₂ = b ≫ d 0 1`,
their classes under `homologyπ 1` agree. Uses the Mathlib boundary-vanishing
lemma `HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary` via
subtraction and `sub_eq_zero`; no finite comparison or ordinary-H1 bridge is used.

Nonclaims: no Kummer, motivic, étale, or isomorphism statement. -/
theorem homogeneousCochains_boundary_class_eq
    (X : TopRep k G) {A : TopModuleCat k}
    (z₁ z₂ : A ⟶ (TopRep.homogeneousCochains X).X 1)
    (b : A ⟶ (TopRep.homogeneousCochains X).X 0)
    (hz₁ : z₁ ≫ (TopRep.homogeneousCochains X).d 1 2 = 0)
    (hz₂ : z₂ ≫ (TopRep.homogeneousCochains X).d 1 2 = 0)
    (hsub : z₁ - z₂ = b ≫ (TopRep.homogeneousCochains X).d 0 1) :
    (TopRep.homogeneousCochains X).liftCycles z₁ 2 (by simp) hz₁ ≫
      (TopRep.homogeneousCochains X).homologyπ 1 =
    (TopRep.homogeneousCochains X).liftCycles z₂ 2 (by simp) hz₂ ≫
      (TopRep.homogeneousCochains X).homologyπ 1 := by
  have hcycle : (z₁ - z₂) ≫ (TopRep.homogeneousCochains X).d 1 2 = 0 := by
    rw [hsub, Category.assoc, (TopRep.homogeneousCochains X).d_comp_d,
      CategoryTheory.Limits.comp_zero]
  have hvan :
      (TopRep.homogeneousCochains X).liftCycles (z₁ - z₂) 2 (by simp) hcycle ≫
        (TopRep.homogeneousCochains X).homologyπ 1 = 0 :=
    (TopRep.homogeneousCochains X).liftCycles_homologyπ_eq_zero_of_boundary
      (z₁ - z₂) 2 (by simp) b hsub
  have hsub_lift :
      (TopRep.homogeneousCochains X).liftCycles (z₁ - z₂) 2 (by simp) hcycle =
      (TopRep.homogeneousCochains X).liftCycles z₁ 2 (by simp) hz₁ -
        (TopRep.homogeneousCochains X).liftCycles z₂ 2 (by simp) hz₂ := by
    apply (cancel_mono ((TopRep.homogeneousCochains X).iCycles 1)).mp
    rw [HomologicalComplex.liftCycles_i, Preadditive.sub_comp,
      HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  have hsub_class :
      ((TopRep.homogeneousCochains X).liftCycles z₁ 2 (by simp) hz₁ ≫
        (TopRep.homogeneousCochains X).homologyπ 1) -
      ((TopRep.homogeneousCochains X).liftCycles z₂ 2 (by simp) hz₂ ≫
        (TopRep.homogeneousCochains X).homologyπ 1) = 0 := by
    rw [← Preadditive.sub_comp, ← hsub_lift, hvan]
  exact sub_eq_zero.mp hsub_class

/-- Rank-one zero-class boundary converse for continuous degree-one cohomology.

Given a homogeneous degree-one element `y` with rank-one cocycle morphism
`z = ofHom ((toSpanSingleton k y).comp uliftDown)`, a cycle proof `hz`, and a zero-class
hypothesis `hzero` for the lifted cycle under `homologyπ 1`, there is an
explicit degree-zero rank-one morphism `w` with `z = w ≫ d 0 1`.

Reuses `HomologicalComplex.homologyIsCokernel 0 1`,
`TopModuleCat.isColimitCoker` with `TopModuleCat.cokerπ`,
`CategoryTheory.IsColimit.comp_coconePointUniqueUpToIso_hom`,
`HomologicalComplex.liftCycles` with `K.toCycles` and `K.homologyπ`,
`Submodule.Quotient.mk_eq_zero`, `HomologicalComplex.liftCycles_i`,
`HomologicalComplex.toCycles_i`, and
`ContinuousLinearMap.toSpanSingleton` round-trip facts. The rank-one domain is
the universe-raised `TopModuleCat.of k (ULift k)`.

Nonclaims: no Kummer, motivic, etale, or comparison statement; rank-one
domain only; no higher-weight statement. -/
theorem rankOne_zeroClass_eq_boundary
    (X : TopRep.{max v (max u w), u, v} k G)
    (y : (TopRep.homogeneousCochains.{u, v, max u w} X).X 1)
    (hz : TopModuleCat.ofHom
      ((ContinuousLinearMap.toSpanSingleton k y).comp uliftDown.{u, max v (max u w)} :
        ULift.{max v (max u w), u} k →L[k] _) ≫
      (TopRep.homogeneousCochains.{u, v, max u w} X).d 1 2 = 0)
    (hzero : (TopRep.homogeneousCochains.{u, v, max u w} X).liftCycles
      (TopModuleCat.ofHom
        ((ContinuousLinearMap.toSpanSingleton k y).comp
          uliftDown.{u, max v (max u w)} :
        ULift.{max v (max u w), u} k →L[k] _))
        2 (by simp) hz ≫
      (TopRep.homogeneousCochains.{u, v, max u w} X).homologyπ 1 = 0) :
    ∃ w : TopModuleCat.of k (ULift.{max v (max u w), u} k) ⟶
        (TopRep.homogeneousCochains.{u, v, max u w} X).X 0,
      TopModuleCat.ofHom
        ((ContinuousLinearMap.toSpanSingleton k y).comp
          uliftDown.{u, max v (max u w)} :
        ULift.{max v (max u w), u} k →L[k] _) =
        w ≫ (TopRep.homogeneousCochains.{u, v, max u w} X).d 0 1 := by
  let K := TopRep.homogeneousCochains.{u, v, max u w} X
  let z := TopModuleCat.ofHom
    ((ContinuousLinearMap.toSpanSingleton k y).comp
      uliftDown.{u, max v (max u w)})
  have h_next1 : (ComplexShape.up ℕ).next 1 = 2 := (ComplexShape.up ℕ).next_eq' rfl
  have h_prev1 : (ComplexShape.up ℕ).prev 1 = 0 := (ComplexShape.up ℕ).prev_eq' rfl
  have hCoker := K.homologyIsCokernel 0 1 h_prev1
  let cyc : TopModuleCat.of k (ULift.{max v (max u w), u} k) ⟶ K.cycles 1 :=
    K.liftCycles z 2 h_next1 hz
  have hzeroK : cyc ≫ K.homologyπ 1 = 0 := hzero
  -- Both `K.homologyπ 1` and `TopModuleCat.cokerπ (K.toCycles 0 1)` are
  -- cokernels of `K.toCycles 0 1` (`hCoker` and `TopModuleCat.isColimitCoker _`);
  -- transfer vanishing across the unique iso to the concrete cokernel.
  have h_coker_zero : cyc ≫ TopModuleCat.cokerπ (K.toCycles 0 1) = 0 := by
    have hcolim2 := TopModuleCat.isColimitCoker (K.toCycles 0 1)
    let iso := CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso hCoker hcolim2
    have hbase := CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
      hCoker hcolim2 CategoryTheory.Limits.WalkingParallelPair.one
    have h_ofπ_homology : ((CategoryTheory.Limits.CokernelCofork.ofπ (K.homologyπ 1)
      (K.toCycles_comp_homologyπ 0 1)).ι.app
      CategoryTheory.Limits.WalkingParallelPair.one) = K.homologyπ 1 := rfl
    have h_ofπ_coker : ((CategoryTheory.Limits.CokernelCofork.ofπ
      (TopModuleCat.cokerπ (K.toCycles 0 1))
      (TopModuleCat.comp_cokerπ (K.toCycles 0 1))).ι.app
      CategoryTheory.Limits.WalkingParallelPair.one) =
      TopModuleCat.cokerπ (K.toCycles 0 1) := rfl
    have h_eq : TopModuleCat.cokerπ (K.toCycles 0 1)
        = K.homologyπ 1 ≫ iso.hom := by
      rw [h_ofπ_homology, h_ofπ_coker] at hbase
      exact hbase.symm
    have h_transfer : cyc ≫ TopModuleCat.cokerπ (K.toCycles 0 1)
        = cyc ≫ K.homologyπ 1 ≫ iso.hom :=
      congrArg (cyc ≫ ·) h_eq
    rw [h_transfer, ← Category.assoc, hzeroK, CategoryTheory.Limits.zero_comp]
  have h_c1 : (TopModuleCat.cokerπ (K.toCycles 0 1)).hom
      (cyc.hom (ULift.up.{max v (max u w), u} (1 : k))) = 0 := by
    have h_comp : (cyc ≫ TopModuleCat.cokerπ (K.toCycles 0 1)).hom
        (ULift.up.{max v (max u w), u} (1 : k)) = 0 := by simp [h_coker_zero]
    simpa [TopModuleCat.hom_comp] using h_comp
  have h_mk : Submodule.mkQ (K.toCycles 0 1).hom.range
      (cyc.hom (ULift.up.{max v (max u w), u} (1 : k))) = 0 := by
    rw [← TopModuleCat.hom_cokerπ]; exact h_c1
  obtain ⟨w0, hw0⟩ := (Submodule.Quotient.mk_eq_zero
    (p := (K.toCycles 0 1).hom.range)).mp
    (by rw [← Submodule.mkQ_apply]; exact h_mk)
  -- Witness natively in `K.X 0`, avoiding any `S.X₁` transport.
  have hw0' : (K.toCycles 0 1).hom w0 = cyc.hom (ULift.up.{max v (max u w), u} (1 : k)) := by
    exact hw0
  have h_r : ∀
      (f : TopModuleCat.of k (ULift.{max v (max u w), u} k) ⟶ K.cycles 1)
      (r : ULift.{max v (max u w), u} k),
      f.hom r = r.down • f.hom (ULift.up.{max v (max u w), u} (1 : k)) := by
    intro f r
    have hr : r.down •
        (ULift.up.{max v (max u w), u} (1 : k) :
          ULift.{max v (max u w), u} k) = r := by
      apply ULift.ext
      change r.down • (1 : k) = r.down
      rw [smul_eq_mul, mul_one]
    conv_lhs => rw [← hr]
    rw [map_smul]
  have hw_r : ∀ (r : ULift.{max v (max u w), u} k),
      (TopModuleCat.ofHom
        ((ContinuousLinearMap.toSpanSingleton k w0).comp
          uliftDown.{u, max v (max u w)} :
        ULift.{max v (max u w), u} k →L[k] K.X 0)).hom r = r.down • w0 := by
    intro r
    simp only [TopModuleCat.hom_ofHom, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, uliftDown]
    rfl
  let w : TopModuleCat.of k (ULift.{max v (max u w), u} k) ⟶ K.X 0 :=
    TopModuleCat.ofHom
      ((ContinuousLinearMap.toSpanSingleton k w0).comp
        uliftDown.{u, max v (max u w)})
  have h_w_toCycles : w ≫ K.toCycles 0 1 = cyc := by
    apply (CategoryTheory.cancel_mono (K.iCycles 1)).mp
    ext r
    have h1 : (w ≫ K.toCycles 0 1).hom r
        = r.down • cyc.hom (ULift.up.{max v (max u w), u} (1 : k)) := by
      rw [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply]
      have hw_r_w : w.hom r = r.down • w0 := hw_r r
      rw [hw_r_w, map_smul]
      congr 1
    have h_left : ((w ≫ K.toCycles 0 1) ≫ K.iCycles 1).hom r
        = r.down • (K.iCycles 1).hom (cyc.hom (ULift.up.{max v (max u w), u} (1 : k))) := by
      rw [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply, h1, map_smul]
    have h_right : (cyc ≫ K.iCycles 1).hom r
        = r.down • (K.iCycles 1).hom (cyc.hom (ULift.up.{max v (max u w), u} (1 : k))) := by
      rw [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply, h_r cyc r, map_smul]
    rw [h_left, h_right]
  have h_cyc_eq : cyc = w ≫ K.toCycles 0 1 := h_w_toCycles.symm
  refine ⟨w, ?_⟩
  have h_lift : cyc ≫ K.iCycles 1 = z :=
    HomologicalComplex.liftCycles_i K z 2 h_next1 hz
  rw [← HomologicalComplex.toCycles_i, ← Category.assoc, ← h_cyc_eq]
  exact h_lift.symm

end ContinuousCohomology
