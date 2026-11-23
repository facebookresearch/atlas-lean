/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.CGWHWeakHSpaceFundamentalGroup
public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction

/-!
# Positive homotopy groups of weak H-spaces

Construct multiplication on based cube classes using the native CGWH
product and homotopies relative to the cube boundary. The weak unit paths
transport multiplication back to the chosen basepoint; interchange gives
commutativity on positive homotopy groups.

A homotopy from the identity to the native doubling map, with the prescribed
inverse root trace, makes these positive homotopy groups trivial. The
construction retains the shifted unit, root paths, and original product.
-/

@[expose] public section

universe w k

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval Topology Topology.Homotopy

namespace CGWH.WeakHSpaceData

section Part1


variable {Y : CGWH.{w, k}} (H : CGWH.WeakHSpaceData Y)

/-- Lifted compact cubes are actual native parameter objects in the carrier universe. -/
abbrev liftedCube (n : ℕ) : CGWH.{w, k} :=
  CGWH.of (ULift.{k, 0} (Fin n → unitInterval))

/-- The same compact parameter object for a relative cube homotopy. -/
abbrev liftedCubeCylinder (n : ℕ) : CGWH.{w, k} :=
  CGWH.of (ULift.{k, 0} (unitInterval × (Fin n → unitInterval)))

/-- A generalized loop gives its actual morphism from the lifted compact cube. -/
def cubeHom (n : ℕ) (p : GenLoop (Fin n) Y H.e) : liftedCube.{w, k} n ⟶ Y :=
  ConcreteCategory.ofHom
    ⟨fun t => p t.down, p.val.continuous.comp continuous_uliftDown⟩

/-- Pair the two actual generalized loops using the categorical native product. -/
def cubePair (n : ℕ) (p q : GenLoop (Fin n) Y H.e) :
    liftedCube.{w, k} n ⟶ Y ⨯ Y :=
  Limits.prod.lift (cubeHom H n p) (cubeHom H n q)

@[simp]
theorem cubePair_apply (n : ℕ) (p q : GenLoop (Fin n) Y H.e)
    (t : Fin n → unitInterval) :
    cubePair H n p q (ULift.up t) = CGWH.prodPoint Y Y (p t) (q t) := by
  rw [cubePair, CGWH.prod_lift_apply]
  rfl

/-- Pointwise cube multiplication lands at the actual product basepoint, before transport. -/
def rawCubeMul (n : ℕ) (p q : GenLoop (Fin n) Y H.e) :
    GenLoop (Fin n) Y H.mulUnit :=
  ⟨⟨fun t => (cubePair H n p q ≫ H.mul) (ULift.up t),
      (CGWH.cgwhToTop.{w, k}.map (cubePair H n p q ≫ H.mul)).hom.continuous.comp
        continuous_uliftUp⟩, by
    intro t ht
    change (cubePair H n p q ≫ H.mul) (ULift.up t) = H.mulUnit
    have hp : p t = H.e := GenLoop.boundary p t ht
    have hq : q t = H.e := GenLoop.boundary q t ht
    have hEval : (cubePair H n p q ≫ H.mul) (ULift.up t) =
        H.mul (CGWH.prodPoint Y Y (p t) (q t)) :=
      (CategoryTheory.comp_apply (C := CGWH.{w, k})
        (cubePair H n p q) H.mul (ULift.up t)).trans
        (congrArg (fun y : ↑(Y ⨯ Y : CGWH.{w, k}) =>
          (CGWH.cgwhToTop.{w, k}.map H.mul).hom y) (cubePair_apply H n p q t))
    exact hEval.trans
      (congrArg₂ (fun x y : Y => H.mul (CGWH.prodPoint Y Y x y)) hp hq)⟩

@[simp]
theorem rawCubeMul_apply (n : ℕ) (p q : GenLoop (Fin n) Y H.e)
    (t : Fin n → unitInterval) :
    rawCubeMul H n p q t = H.mul (CGWH.prodPoint Y Y (p t) (q t)) := by
  change (cubePair H n p q ≫ H.mul) (ULift.up t) = _
  exact (CategoryTheory.comp_apply (C := CGWH.{w, k})
    (cubePair H n p q) H.mul (ULift.up t)).trans
    (congrArg (fun y : ↑(Y ⨯ Y : CGWH.{w, k}) =>
          (CGWH.cgwhToTop.{w, k}.map H.mul).hom y) (cubePair_apply H n p q t))

/-- The genuine relative cube homotopies pair as maps from the lifted compact cylinder. -/
def cubeHomotopyPair (n : ℕ) {p₀ p₁ q₀ q₁ : GenLoop (Fin n) Y H.e}
    (P : p₀.val.HomotopyRel p₁.val (Cube.boundary (Fin n)))
    (Q : q₀.val.HomotopyRel q₁.val (Cube.boundary (Fin n))) :
    liftedCubeCylinder.{w, k} n ⟶ Y ⨯ Y :=
  Limits.prod.lift
    (ConcreteCategory.ofHom
      ⟨fun st => P st.down, P.continuous.comp continuous_uliftDown⟩)
    (ConcreteCategory.ofHom
      ⟨fun st => Q st.down, Q.continuous.comp continuous_uliftDown⟩)

@[simp]
theorem cubeHomotopyPair_apply (n : ℕ) {p₀ p₁ q₀ q₁ : GenLoop (Fin n) Y H.e}
    (P : p₀.val.HomotopyRel p₁.val (Cube.boundary (Fin n)))
    (Q : q₀.val.HomotopyRel q₁.val (Cube.boundary (Fin n)))
    (st : unitInterval × (Fin n → unitInterval)) :
    cubeHomotopyPair H n P Q (ULift.up st) = CGWH.prodPoint Y Y (P st) (Q st) := by
  rw [cubeHomotopyPair, CGWH.prod_lift_apply]
  rfl

/-- Native pointwise multiplication preserves actual homotopies relative to the boundary. -/
def rawCubeMulHomotopy (n : ℕ) {p₀ p₁ q₀ q₁ : GenLoop (Fin n) Y H.e}
    (P : p₀.val.HomotopyRel p₁.val (Cube.boundary (Fin n)))
    (Q : q₀.val.HomotopyRel q₁.val (Cube.boundary (Fin n))) :
    (rawCubeMul H n p₀ q₀).val.HomotopyRel (rawCubeMul H n p₁ q₁).val
      (Cube.boundary (Fin n)) where
  toFun st := (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up st)
  continuous_toFun :=
    (CGWH.cgwhToTop.{w, k}.map (cubeHomotopyPair H n P Q ≫ H.mul)).hom.continuous.comp
      continuous_uliftUp
  map_zero_left t := by
    change (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up (0, t)) =
      (rawCubeMul H n p₀ q₀).val t
    have hP : P (0, t) = p₀ t := P.apply_zero t
    have hQ : Q (0, t) = q₀ t := Q.apply_zero t
    have hEval : (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up (0, t)) =
        H.mul (CGWH.prodPoint Y Y (P (0, t)) (Q (0, t))) :=
      (CategoryTheory.comp_apply (C := CGWH.{w, k})
        (cubeHomotopyPair H n P Q) H.mul (ULift.up (0, t))).trans
        (congrArg (fun y : ↑(Y ⨯ Y : CGWH.{w, k}) =>
          (CGWH.cgwhToTop.{w, k}.map H.mul).hom y) (cubeHomotopyPair_apply H n P Q (0, t)))
    exact hEval.trans ((congrArg₂
      (fun x y : Y => H.mul (CGWH.prodPoint Y Y x y)) hP hQ).trans
        (rawCubeMul_apply H n p₀ q₀ t).symm)
  map_one_left t := by
    change (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up (1, t)) =
      (rawCubeMul H n p₁ q₁).val t
    have hP : P (1, t) = p₁ t := P.apply_one t
    have hQ : Q (1, t) = q₁ t := Q.apply_one t
    have hEval : (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up (1, t)) =
        H.mul (CGWH.prodPoint Y Y (P (1, t)) (Q (1, t))) :=
      (CategoryTheory.comp_apply (C := CGWH.{w, k})
        (cubeHomotopyPair H n P Q) H.mul (ULift.up (1, t))).trans
        (congrArg (fun y : ↑(Y ⨯ Y : CGWH.{w, k}) =>
          (CGWH.cgwhToTop.{w, k}.map H.mul).hom y) (cubeHomotopyPair_apply H n P Q (1, t)))
    exact hEval.trans ((congrArg₂
      (fun x y : Y => H.mul (CGWH.prodPoint Y Y x y)) hP hQ).trans
        (rawCubeMul_apply H n p₁ q₁ t).symm)
  prop' t x hx := by
    change (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up (t, x)) =
      (rawCubeMul H n p₀ q₀).val x
    have hP : P (t, x) = p₀ x := P.eq_fst t hx
    have hQ : Q (t, x) = q₀ x := Q.eq_fst t hx
    have hEval : (cubeHomotopyPair H n P Q ≫ H.mul) (ULift.up (t, x)) =
        H.mul (CGWH.prodPoint Y Y (P (t, x)) (Q (t, x))) :=
      (CategoryTheory.comp_apply (C := CGWH.{w, k})
        (cubeHomotopyPair H n P Q) H.mul (ULift.up (t, x))).trans
        (congrArg (fun y : ↑(Y ⨯ Y : CGWH.{w, k}) =>
          (CGWH.cgwhToTop.{w, k}.map H.mul).hom y) (cubeHomotopyPair_apply H n P Q (t, x)))
    exact hEval.trans ((congrArg₂
      (fun x y : Y => H.mul (CGWH.prodPoint Y Y x y)) hP hQ).trans
        (rawCubeMul_apply H n p₀ q₀ x).symm)

/-- The raw product operation respects the original generalized-loop homotopy relation. -/
theorem rawCubeMul_rel (n : ℕ) {p₀ p₁ q₀ q₁ : GenLoop (Fin n) Y H.e}
    (hp : GenLoop.Homotopic p₀ p₁) (hq : GenLoop.Homotopic q₀ q₁) :
    GenLoop.Homotopic (rawCubeMul H n p₀ q₀) (rawCubeMul H n p₁ q₁) := by
  obtain ⟨P⟩ := hp
  obtain ⟨Q⟩ := hq
  exact ⟨rawCubeMulHomotopy H n P Q⟩

/-- This is the actual cube-class product at the product point; no transport is supplied. -/
def rawCubeClassMul (n : ℕ) (p q : HomotopyGroup.Pi n Y H.e) :
    HomotopyGroup.Pi n Y H.mulUnit :=
  _root_.Quotient.map₂ (rawCubeMul H n) (by
    intro _ _ hp _ _ hq
    exact rawCubeMul_rel H n hp hq) p q

private theorem rawCubeClassMul_mk (n : ℕ) (p q : GenLoop (Fin n) Y H.e) :
    rawCubeClassMul H n (HomotopyGroup.mk p) (HomotopyGroup.mk q) =
      HomotopyGroup.mk (rawCubeMul H n p q) := rfl

/-- Pointwise multiplication commutes with concatenation in every actual cube direction. -/
theorem rawCubeMul_transAt (n : ℕ) (i : Fin n)
    (p p' q q' : GenLoop (Fin n) Y H.e) :
    rawCubeMul H n (GenLoop.transAt i p p') (GenLoop.transAt i q q') =
      GenLoop.transAt i (rawCubeMul H n p q) (rawCubeMul H n p' q') := by
  apply GenLoop.ext
  intro t
  simp only [rawCubeMul_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

end Part1

section Part2


variable {Y : CGWH.{w, k}} (H : CGWH.WeakHSpaceData Y)

/-- The raw product at the multiplication point distributes over the actual cube group law. -/
theorem rawCubeClassMul_interchange (n : ℕ)
    (a b c d : HomotopyGroup.Pi (n + 1) Y H.e) :
    rawCubeClassMul H (n + 1) (a * b) (c * d) =
      rawCubeClassMul H (n + 1) a c * rawCubeClassMul H (n + 1) b d := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective b
  obtain ⟨r, rfl⟩ := HomotopyGroup.mk_surjective c
  obtain ⟨s, rfl⟩ := HomotopyGroup.mk_surjective d
  simp only [rawCubeClassMul_mk, HomotopyGroup.mul_mk (0 : Fin (n + 1))]
  exact congrArg HomotopyGroup.mk (rawCubeMul_transAt H (n + 1) 0 q p s r)

/-- The selected-unit operation uses the existing actual root-path group equivalence. -/
def cubeMul (n : ℕ) (a b : HomotopyGroup.Pi (n + 1) Y H.e) :
    HomotopyGroup.Pi (n + 1) Y H.e :=
  TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) H.rootPath
    (rawCubeClassMul H (n + 1) a b)

/-- Transported interchange follows from the actual multiplicative path-change equivalence. -/
theorem cubeMul_interchange (n : ℕ) (a b c d : HomotopyGroup.Pi (n + 1) Y H.e) :
    cubeMul H n (a * b) (c * d) = cubeMul H n a c * cubeMul H n b d := by
  let E : HomotopyGroup.Pi (n + 1) Y H.mulUnit ≃* HomotopyGroup.Pi (n + 1) Y H.e :=
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) H.rootPath
  exact (congrArg E (rawCubeClassMul_interchange H n a b c d)).trans
    (E.map_mul (rawCubeClassMul H (n + 1) a c) (rawCubeClassMul H (n + 1) b d))

end Part2

section Part3


private def mappedCubeOfEq
    {A B : Type k} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (n : ℕ) (f : C(A, B)) (hf : f a = b)
    (p : GenLoop (Fin n) A a) : GenLoop (Fin n) B b :=
  ⟨f.comp p.val, by
    intro t ht
    change f (p t) = b
    exact (congrArg f (p.property t ht)).trans hf⟩

private theorem mapHomOfEq_mk_mappedCube
    {A B : Type k} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (n : ℕ) (f : C(A, B)) (hf : f a = b)
    (p : GenLoop (Fin (n + 1)) A a) :
    HomotopyGroup.mapHomOfEq f hf n (HomotopyGroup.mk p) =
      HomotopyGroup.mk (mappedCubeOfEq (n + 1) f hf p) := by
  cases hf
  rfl

variable {Y : CGWH.{w, k}} (H : CGWH.WeakHSpaceData Y)

/-- Raw left multiplication by the constant cube is the genuine induced
left-unit map, with its image basepoint aligned to the native product point. -/
theorem rawCubeClassMul_one_left_map (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    rawCubeClassMul H (n + 1) 1 a =
      HomotopyGroup.mapHomOfEq
        (CGWH.cgwhToTop.{w, k}.map (CGWH.hspaceLeftUnitMap Y H.mul H.e)).hom
        H.leftUnitMap_unit n a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  let f : C(Y, Y) :=
    (CGWH.cgwhToTop.{w, k}.map (CGWH.hspaceLeftUnitMap Y H.mul H.e)).hom
  have hf : f H.e = H.mulUnit := H.leftUnitMap_unit
  have hMapped : HomotopyGroup.mapHomOfEq f hf n (HomotopyGroup.mk p) =
      HomotopyGroup.mk (mappedCubeOfEq (n + 1) f hf p) :=
    mapHomOfEq_mk_mappedCube n f hf p
  have hLoop : rawCubeMul H (n + 1) GenLoop.const p = mappedCubeOfEq (n + 1) f hf p := by
    apply GenLoop.ext
    intro t
    have hRaw := rawCubeMul_apply H (n + 1) GenLoop.const p t
    change rawCubeMul H (n + 1) GenLoop.const p t = f (p t)
    exact hRaw.trans (CGWH.hspaceLeftUnitMap_apply Y H.mul H.e (p t)).symm
  have hClass : rawCubeClassMul H (n + 1) 1 (HomotopyGroup.mk p) =
      HomotopyGroup.mk (rawCubeMul H (n + 1) GenLoop.const p) := by
    rewrite [HomotopyGroup.one_eq_mk_const]
    exact rawCubeClassMul_mk H (n + 1) GenLoop.const p
  exact hClass.trans ((congrArg HomotopyGroup.mk hLoop).trans hMapped.symm)

/-- The same representative-level formula for the right-unit map. -/
theorem rawCubeClassMul_one_right_map (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    rawCubeClassMul H (n + 1) a 1 =
      HomotopyGroup.mapHomOfEq
        (CGWH.cgwhToTop.{w, k}.map (CGWH.hspaceRightUnitMap Y H.mul H.e)).hom
        H.rightUnitMap_unit n a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  let f : C(Y, Y) :=
    (CGWH.cgwhToTop.{w, k}.map (CGWH.hspaceRightUnitMap Y H.mul H.e)).hom
  have hf : f H.e = H.mulUnit := H.rightUnitMap_unit
  have hMapped : HomotopyGroup.mapHomOfEq f hf n (HomotopyGroup.mk p) =
      HomotopyGroup.mk (mappedCubeOfEq (n + 1) f hf p) :=
    mapHomOfEq_mk_mappedCube n f hf p
  have hLoop : rawCubeMul H (n + 1) p GenLoop.const = mappedCubeOfEq (n + 1) f hf p := by
    apply GenLoop.ext
    intro t
    have hRaw := rawCubeMul_apply H (n + 1) p GenLoop.const t
    change rawCubeMul H (n + 1) p GenLoop.const t = f (p t)
    exact hRaw.trans (CGWH.hspaceRightUnitMap_apply Y H.mul H.e (p t)).symm
  have hClass : rawCubeClassMul H (n + 1) (HomotopyGroup.mk p) 1 =
      HomotopyGroup.mk (rawCubeMul H (n + 1) p GenLoop.const) := by
    rewrite [HomotopyGroup.one_eq_mk_const]
    exact rawCubeClassMul_mk H (n + 1) p GenLoop.const
  exact hClass.trans ((congrArg HomotopyGroup.mk hLoop).trans hMapped.symm)

/-- The transported cube product has a left unit, derived from the actual
left-unit homotopy and its proved root-path trace. -/
theorem cubeMul_one_left (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    cubeMul H n 1 a = a := by
  let Z : TopCat.{k} := TopCat.of Y
  let f : C(Y, Y) :=
    (CGWH.cgwhToTop.{w, k}.map (CGWH.hspaceLeftUnitMap Y H.mul H.e)).hom
  have hf : f H.e = H.mulUnit := H.leftUnitMap_unit
  let K : TopCat.Homotopy (TopCat.ofHom f : Z ⟶ Z) (𝟙 Z) := H.leftUnit
  have hUnit := TopCat.homotopyGroup_map_homotopy_trace_of_eq
    (X := Z) (Y := Z) (f := TopCat.ofHom f) (g := 𝟙 Z)
    n K H.e hf rfl a
  have hTrace : ((K.evalAt H.e).cast hf.symm rfl) =
      CGWH.hspaceLeftUnitPath Y H.mul H.e H.leftUnit := rfl
  have hId : HomotopyGroup.mapHomOfEq (ContinuousMap.id Y) rfl n a = a :=
    HomotopyGroup.mapHomOfEq_id H.e n a
  have hUnit' : TopCat.homotopyGroupBasepointChangeMulEquiv n Z
      (CGWH.hspaceLeftUnitPath Y H.mul H.e H.leftUnit)
      (HomotopyGroup.mapHomOfEq f hf n a) = a := by
    rewrite [hTrace] at hUnit
    exact hUnit.trans hId
  have hRoot := TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n Z H.leftUnit_root
  let E : HomotopyGroup.Pi (n + 1) Y H.mulUnit ≃* HomotopyGroup.Pi (n + 1) Y H.e :=
    TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath
  have h1 : cubeMul H n 1 a = E (HomotopyGroup.mapHomOfEq f hf n a) :=
    congrArg E (rawCubeClassMul_one_left_map H n a)
  have h2 : E (HomotopyGroup.mapHomOfEq f hf n a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Z
        (CGWH.hspaceLeftUnitPath Y H.mul H.e H.leftUnit)
        (HomotopyGroup.mapHomOfEq f hf n a) :=
    congrArg (fun e : HomotopyGroup.Pi (n + 1) Y H.mulUnit ≃*
      HomotopyGroup.Pi (n + 1) Y H.e => e (HomotopyGroup.mapHomOfEq f hf n a)) hRoot.symm
  exact h1.trans (h2.trans hUnit')

/-- The transported cube product has a right unit, from the actual
right-unit homotopy and its root trace. -/
theorem cubeMul_one_right (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    cubeMul H n a 1 = a := by
  let Z : TopCat.{k} := TopCat.of Y
  let f : C(Y, Y) :=
    (CGWH.cgwhToTop.{w, k}.map (CGWH.hspaceRightUnitMap Y H.mul H.e)).hom
  have hf : f H.e = H.mulUnit := H.rightUnitMap_unit
  let K : TopCat.Homotopy (TopCat.ofHom f : Z ⟶ Z) (𝟙 Z) := H.rightUnit
  have hUnit := TopCat.homotopyGroup_map_homotopy_trace_of_eq
    (X := Z) (Y := Z) (f := TopCat.ofHom f) (g := 𝟙 Z)
    n K H.e hf rfl a
  have hTrace : ((K.evalAt H.e).cast hf.symm rfl) =
      CGWH.hspaceRightUnitPath Y H.mul H.e H.rightUnit := rfl
  have hId : HomotopyGroup.mapHomOfEq (ContinuousMap.id Y) rfl n a = a :=
    HomotopyGroup.mapHomOfEq_id H.e n a
  have hUnit' : TopCat.homotopyGroupBasepointChangeMulEquiv n Z
      (CGWH.hspaceRightUnitPath Y H.mul H.e H.rightUnit)
      (HomotopyGroup.mapHomOfEq f hf n a) = a := by
    rewrite [hTrace] at hUnit
    exact hUnit.trans hId
  have hRoot := TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n Z H.rightUnit_root
  let E : HomotopyGroup.Pi (n + 1) Y H.mulUnit ≃* HomotopyGroup.Pi (n + 1) Y H.e :=
    TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath
  have h1 : cubeMul H n a 1 = E (HomotopyGroup.mapHomOfEq f hf n a) :=
    congrArg E (rawCubeClassMul_one_right_map H n a)
  have h2 : E (HomotopyGroup.mapHomOfEq f hf n a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Z
        (CGWH.hspaceRightUnitPath Y H.mul H.e H.rightUnit)
        (HomotopyGroup.mapHomOfEq f hf n a) :=
    congrArg (fun e : HomotopyGroup.Pi (n + 1) Y H.mulUnit ≃*
      HomotopyGroup.Pi (n + 1) Y H.e => e (HomotopyGroup.mapHomOfEq f hf n a)) hRoot.symm
  exact h1.trans (h2.trans hUnit')

/-- The two derived unit equations are ordinary Eckmann-Hilton hypotheses. -/
theorem cubeMul_isUnital (n : ℕ) :
    EckmannHilton.IsUnital (cubeMul H n) (1 : HomotopyGroup.Pi (n + 1) Y H.e) :=
  { left_id := cubeMul_one_left H n
    right_id := cubeMul_one_right H n }

/-- The actual root-transported pointwise cube product equals the native
homotopy-group multiplication, in its existing reversed-concatenation order. -/
theorem cubeMul_eq_mul (n : ℕ) (a b : HomotopyGroup.Pi (n + 1) Y H.e) :
    cubeMul H n a b = a * b := by
  have h : cubeMul H n =
      (fun a b : HomotopyGroup.Pi (n + 1) Y H.e => a * b) :=
    EckmannHilton.mul (cubeMul_isUnital H n) EckmannHilton.MulOneClass.isUnital
      (cubeMul_interchange H n)
  exact congrFun (congrFun h a) b

/-- Eckmann-Hilton gives commutativity in every positive degree, including
degree one, without an installed global commutative-group instance. -/
theorem positiveGroup_mul_comm (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 1) Y H.e) : a * b = b * a :=
  (EckmannHilton.mul_comm (cubeMul_isUnital H n)
    EckmannHilton.MulOneClass.isUnital (cubeMul_interchange H n)).comm a b

/-- The doubled map is literally the native product diagonal followed by
the given multiplication. -/
def nativeDoubling : Y ⟶ Y :=
  Limits.prod.lift (𝟙 Y) (𝟙 Y) ≫ H.mul

/-- Its value at the selected unit is the actual multiplication point. -/
theorem nativeDoubling_unit : nativeDoubling H H.e = H.mulUnit := by
  rewrite [nativeDoubling, CategoryTheory.comp_apply, CGWH.prod_lift_apply]
  rfl

/-- The induced doubled map is the raw diagonal cube product, before any
root-path transport. -/
theorem rawCubeClassMul_diagonal_map (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    HomotopyGroup.mapHomOfEq (CGWH.cgwhToTop.{w, k}.map (nativeDoubling H)).hom
        (nativeDoubling_unit H) n a =
      rawCubeClassMul H (n + 1) a a := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  let f : C(Y, Y) := (CGWH.cgwhToTop.{w, k}.map (nativeDoubling H)).hom
  have hf : f H.e = H.mulUnit := nativeDoubling_unit H
  have hMapped : HomotopyGroup.mapHomOfEq f hf n (HomotopyGroup.mk p) =
      HomotopyGroup.mk (mappedCubeOfEq (n + 1) f hf p) :=
    mapHomOfEq_mk_mappedCube n f hf p
  have hLoop : mappedCubeOfEq (n + 1) f hf p = rawCubeMul H (n + 1) p p := by
    apply GenLoop.ext
    intro t
    have hDouble : nativeDoubling H (p t) = H.mul (CGWH.prodPoint Y Y (p t) (p t)) := by
      rewrite [nativeDoubling, CategoryTheory.comp_apply, CGWH.prod_lift_apply]
      rfl
    exact hDouble.trans (rawCubeMul_apply H (n + 1) p p t).symm
  exact hMapped.trans ((congrArg HomotopyGroup.mk hLoop).trans
    (rawCubeClassMul_mk H (n + 1) p p).symm)

/-- Transport first along the reversed root and then the root cancels by
the actual endpoint-fixed inverse-path law. -/
theorem rootTransport_symm_cancel (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) Y H.e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) H.rootPath
      (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) H.rootPath.symm a) = a := by
  let Z : TopCat.{k} := TopCat.of Y
  have h1 : TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath
      (TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath.symm a) =
        TopCat.homotopyGroupBasepointChangeMulEquiv n Z (H.rootPath.symm.trans H.rootPath) a :=
    (congrArg (fun E : HomotopyGroup.Pi (n + 1) Y H.e ≃*
      HomotopyGroup.Pi (n + 1) Y H.e => E a)
      (TopCat.homotopyGroupBasepointChangeMulEquiv_trans n Z H.rootPath.symm H.rootPath)).symm
  have h2 : TopCat.homotopyGroupBasepointChangeMulEquiv n Z (H.rootPath.symm.trans H.rootPath) a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Z (Path.refl H.e) a :=
    congrArg (fun E : HomotopyGroup.Pi (n + 1) Y H.e ≃*
      HomotopyGroup.Pi (n + 1) Y H.e => E a)
      (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n Z
        (Path.Homotopic.symm_trans H.rootPath))
  have h3 : TopCat.homotopyGroupBasepointChangeMulEquiv n Z (Path.refl H.e) a = a :=
    congrArg (fun E : HomotopyGroup.Pi (n + 1) Y H.e ≃*
      HomotopyGroup.Pi (n + 1) Y H.e => E a)
      (TopCat.homotopyGroupBasepointChangeMulEquiv_refl n Z H.e)
  exact h1.trans (h2.trans h3)

/-- An actual Id-to-doubling homotopy with its exact inverse-root trace
makes every class idempotent for the transported cube product. -/
theorem cubeMul_diagonal_eq_self
    (J : ContinuousMap.Homotopy (ContinuousMap.id Y)
      (CGWH.cgwhToTop.{w, k}.map (nativeDoubling H)).hom)
    (hTrace : ((J.evalAt H.e).cast rfl (nativeDoubling_unit H).symm).Homotopic H.rootPath.symm)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y H.e) : cubeMul H n a a = a := by
  let Z : TopCat.{k} := TopCat.of Y
  let f : C(Y, Y) := (CGWH.cgwhToTop.{w, k}.map (nativeDoubling H)).hom
  let t := (J.evalAt H.e).cast rfl (nativeDoubling_unit H).symm
  have hMap := TopCat.homotopyGroup_map_homotopy_trace_of_eq
    (X := Z) (Y := Z) (f := 𝟙 Z) (g := TopCat.ofHom f)
    n J H.e rfl (nativeDoubling_unit H) a
  have hId : HomotopyGroup.mapHomOfEq (ContinuousMap.id Y) rfl n a = a :=
    HomotopyGroup.mapHomOfEq_id H.e n a
  have h0 : TopCat.homotopyGroupBasepointChangeMulEquiv n Z t a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Z t
        (HomotopyGroup.mapHomOfEq (ContinuousMap.id Y) rfl n a) :=
    (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n Z t) hId).symm
  have h1 : TopCat.homotopyGroupBasepointChangeMulEquiv n Z t a =
      rawCubeClassMul H (n + 1) a a :=
    h0.trans (hMap.trans (rawCubeClassMul_diagonal_map H n a))
  have h2 : TopCat.homotopyGroupBasepointChangeMulEquiv n Z t a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath.symm a :=
    congrArg (fun E : HomotopyGroup.Pi (n + 1) Y H.e ≃*
      HomotopyGroup.Pi (n + 1) Y H.mulUnit => E a)
      (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n Z hTrace)
  have hRaw : rawCubeClassMul H (n + 1) a a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath.symm a := h1.symm.trans h2
  exact (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n Z H.rootPath) hRaw).trans
    (rootTransport_symm_cancel H n a)

/-- In every positive degree, the actual diagonal homotopy and unit trace
force `a = a*a`; cancellation in the existing group gives `a = 1`. -/
theorem positiveGroup_eq_one
    (J : ContinuousMap.Homotopy (ContinuousMap.id Y)
      (CGWH.cgwhToTop.{w, k}.map (nativeDoubling H)).hom)
    (hTrace : ((J.evalAt H.e).cast rfl (nativeDoubling_unit H).symm).Homotopic
      H.rootPath.symm)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y H.e) : a = 1 := by
  have hIdempotent : a * a = a :=
    (cubeMul_eq_mul H n a a).symm.trans (cubeMul_diagonal_eq_self H J hTrace n a)
  have hCancel : a * a = a * 1 := hIdempotent.trans (mul_one a).symm
  exact mul_left_cancel hCancel

/-- The same genuine argument gives subsingleton positive homotopy groups.
It makes no assertion about connected components or contractibility. -/
theorem positiveGroup_subsingleton
    (J : ContinuousMap.Homotopy (ContinuousMap.id Y)
      (CGWH.cgwhToTop.{w, k}.map (nativeDoubling H)).hom)
    (hTrace : ((J.evalAt H.e).cast rfl (nativeDoubling_unit H).symm).Homotopic
      H.rootPath.symm)
    (n : ℕ) : Subsingleton (HomotopyGroup.Pi (n + 1) Y H.e) := by
  constructor
  intro a b
  exact (positiveGroup_eq_one H J hTrace n a).trans (positiveGroup_eq_one H J hTrace n b).symm

end Part3

end CGWH.WeakHSpaceData

end
