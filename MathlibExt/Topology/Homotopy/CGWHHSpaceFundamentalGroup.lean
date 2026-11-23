/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.ProductPoints
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.EckmannHilton

/-!
# Fundamental groups of native CGWH H-spaces

A native CGWH multiplication has source the categorical product `X ⨯ X`.
The comparison from this product to the ordinary product of underlying spaces
is continuous and bijective, but is not generally a homeomorphism.  Therefore
such a multiplication does not define Mathlib's raw-product `HSpace X`.

This file instead pairs loops and path homotopies through the categorical
product, using lifted compact interval domains.  Pointwise multiplication then
descends to the fundamental group, where the Eckmann--Hilton argument proves
commutativity.  The resulting commutative-group structure is named rather
than installed globally.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits unitInterval

universe u v

namespace CGWH

/-- Constant morphism between CGWH objects. -/
def constMap (X Y : CGWH.{u, v}) (y : Y) : X ⟶ Y :=
  ConcreteCategory.ofHom (ContinuousMap.const X y)

@[simp]
theorem constMap_apply (X Y : CGWH.{u, v}) (y : Y) (x : X) :
    constMap X Y y x = y :=
  rfl

/-- Categorical left multiplication by a selected point. -/
noncomputable def hspaceLeftUnitMap (X : CGWH.{u, v})
    (mul : X ⨯ X ⟶ X) (e : X) : X ⟶ X :=
  Limits.prod.lift (constMap X X e) (𝟙 X) ≫ mul

/-- Categorical right multiplication by a selected point. -/
noncomputable def hspaceRightUnitMap (X : CGWH.{u, v})
    (mul : X ⨯ X ⟶ X) (e : X) : X ⟶ X :=
  Limits.prod.lift (𝟙 X) (constMap X X e) ≫ mul

@[simp]
theorem hspaceLeftUnitMap_apply (X : CGWH.{u, v})
    (mul : X ⨯ X ⟶ X) (e x : X) :
    hspaceLeftUnitMap X mul e x = mul (prodPoint X X e x) := by
  change mul (Limits.prod.lift (constMap X X e) (𝟙 X) x) = _
  rw [prod_lift_apply]
  rfl

@[simp]
theorem hspaceRightUnitMap_apply (X : CGWH.{u, v})
    (mul : X ⨯ X ⟶ X) (e x : X) :
    hspaceRightUnitMap X mul e x = mul (prodPoint X X x e) := by
  change mul (Limits.prod.lift (𝟙 X) (constMap X X e) x) = _
  rw [prod_lift_apply]
  rfl

/-- H-space data whose multiplication is defined on the categorical CGWH
product.  The unit laws are based homotopies of the underlying space. -/
structure HSpaceData (X : CGWH.{u, v}) where
  /-- Native categorical multiplication. -/
  mul : X ⨯ X ⟶ X
  /-- Distinguished unit point. -/
  e : X
  /-- The product of the unit with itself is the unit. -/
  mul_e_e : mul (prodPoint X X e e) = e
  /-- Left unit law, relative to the unit point. -/
  left_unit :
    (ConcreteCategory.hom (hspaceLeftUnitMap X mul e)).HomotopyRel
      (ContinuousMap.id X) {e}
  /-- Right unit law, relative to the unit point. -/
  right_unit :
    (ConcreteCategory.hom (hspaceRightUnitMap X mul e)).HomotopyRel
      (ContinuousMap.id X) {e}

/- These two original public structure fields are used as literal record labels
and projection names downstream. Keep that legacy API rather than renaming data.
The existing lint baseline records precisely these two naming findings. Only this
naming-style check is exempt for these two projections; all other checks run. -/
attribute [nolint defsWithUnderscore] HSpaceData.left_unit HSpaceData.right_unit

namespace HSpaceData

variable {X : CGWH.{u, v}} (H : HSpaceData X)

/-- Construct native H-space data from strict categorical unit laws. -/
noncomputable def ofStrict
    (mul : X ⨯ X ⟶ X) (e : X)
    (mul_e_e : mul (prodPoint X X e e) = e)
    (left_unit : hspaceLeftUnitMap X mul e = 𝟙 X)
    (right_unit : hspaceRightUnitMap X mul e = 𝟙 X) :
    HSpaceData X := by
  have hleft : ConcreteCategory.hom (hspaceLeftUnitMap X mul e) =
      ContinuousMap.id X := by
    apply ContinuousMap.ext
    intro x
    exact ConcreteCategory.congr_hom left_unit x
  have hright : ConcreteCategory.hom (hspaceRightUnitMap X mul e) =
      ContinuousMap.id X := by
    apply ContinuousMap.ext
    intro x
    exact ConcreteCategory.congr_hom right_unit x
  exact
    { mul := mul
      e := e
      mul_e_e := mul_e_e
      left_unit :=
        (ContinuousMap.HomotopyRel.refl
          (ContinuousMap.id X) {e}).cast hleft.symm rfl
      right_unit :=
        (ContinuousMap.HomotopyRel.refl
          (ContinuousMap.id X) {e}).cast hright.symm rfl }

/-- Lifted compact interval as a CGWH parameter object in the carrier
universe of `X`. -/
abbrev liftedUnitInterval : CGWH.{u, v} :=
  CGWH.of (ULift.{v, 0} unitInterval)

/-- Lifted compact square as a CGWH parameter object in the carrier universe
of `X`. -/
abbrev liftedUnitSquare : CGWH.{u, v} :=
  CGWH.of (ULift.{v, 0} (unitInterval × unitInterval))

/-- A path regarded as a CGWH morphism from the lifted compact interval. -/
def pathHom (p : Path H.e H.e) : liftedUnitInterval.{u, v} ⟶ X :=
  ConcreteCategory.ofHom
    ⟨fun t ↦ p t.down, p.continuous.comp continuous_uliftDown⟩

/-- Pair two loops through the categorical CGWH product. -/
noncomputable def pathPair (p q : Path H.e H.e) :
    liftedUnitInterval.{u, v} ⟶ X ⨯ X :=
  Limits.prod.lift (pathHom H p) (pathHom H q)

@[simp]
theorem pathPair_apply (p q : Path H.e H.e) (t : unitInterval) :
    pathPair H p q (ULift.up t) = prodPoint X X (p t) (q t) := by
  rw [pathPair, prod_lift_apply]
  rfl

/-- Pointwise native multiplication of two loops at the distinguished
unit. -/
noncomputable def pathMul (p q : Path H.e H.e) : Path H.e H.e where
  toFun t := (pathPair H p q ≫ H.mul) (ULift.up t)
  continuous_toFun :=
    (ConcreteCategory.hom (pathPair H p q ≫ H.mul)).continuous.comp
      continuous_uliftUp
  source' := by
    rw [CategoryTheory.comp_apply, pathPair_apply, p.source, q.source,
      H.mul_e_e]
  target' := by
    rw [CategoryTheory.comp_apply, pathPair_apply, p.target, q.target,
      H.mul_e_e]

@[simp]
theorem pathMul_apply (p q : Path H.e H.e) (t : unitInterval) :
    pathMul H p q t = H.mul (prodPoint X X (p t) (q t)) := by
  change (pathPair H p q ≫ H.mul) (ULift.up t) = _
  rw [CategoryTheory.comp_apply, pathPair_apply]

/-- A path homotopy regarded as a CGWH morphism from the lifted compact
square. -/
def pathHomotopyHom
    {p₀ p₁ : Path H.e H.e} (P : Path.Homotopy p₀ p₁) :
    liftedUnitSquare.{u, v} ⟶ X :=
  ConcreteCategory.ofHom
    ⟨fun st ↦ P st.down, P.continuous.comp continuous_uliftDown⟩

/-- Pair two path homotopies through the categorical CGWH product. -/
noncomputable def pathHomotopyPair
    {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁) :
    liftedUnitSquare.{u, v} ⟶ X ⨯ X :=
  Limits.prod.lift (pathHomotopyHom H P) (pathHomotopyHom H Q)

@[simp]
theorem pathHomotopyPair_apply
    {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁)
    (st : unitInterval × unitInterval) :
    pathHomotopyPair H P Q (ULift.up st) =
      prodPoint X X (P st) (Q st) := by
  rw [pathHomotopyPair, prod_lift_apply]
  rfl

/-- Pointwise native multiplication of two based path homotopies. -/
noncomputable def pathMulHomotopy
    {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁) :
    Path.Homotopy (pathMul H p₀ q₀) (pathMul H p₁ q₁) where
  toFun st := (pathHomotopyPair H P Q ≫ H.mul) (ULift.up st)
  continuous_toFun :=
    (ConcreteCategory.hom (pathHomotopyPair H P Q ≫ H.mul)).continuous.comp
      continuous_uliftUp
  map_zero_left t := by
    change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (0, t)) =
      pathMul H p₀ q₀ t
    rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
      P.apply_zero, Q.apply_zero, pathMul_apply]
    rfl
  map_one_left t := by
    change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (1, t)) =
      pathMul H p₁ q₁ t
    rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
      P.apply_one, Q.apply_one, pathMul_apply]
    rfl
  prop' s t ht := by
    rcases ht with rfl | rfl
    · change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (s, 0)) =
        pathMul H p₀ q₀ 0
      rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
        P.source, Q.source, H.mul_e_e]
      exact (pathMul H p₀ q₀).source.symm
    · change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (s, 1)) =
        pathMul H p₀ q₀ 1
      rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
        P.target, Q.target, H.mul_e_e]
      exact (pathMul H p₀ q₀).target.symm

/-- Pointwise native multiplication descended to based path-homotopy
classes. -/
noncomputable def fundamentalMul
    (p q : FundamentalGroup X H.e) : FundamentalGroup X H.e :=
  FundamentalGroup.fromPath (Quotient.map₂ (pathMul H)
    (fun _ _ hp _ _ hq ↦ Nonempty.map2 (pathMulHomotopy H) hp hq) p.asHom q.asHom)

@[simp]
theorem fundamentalMul_mk (p q : Path H.e H.e) :
    fundamentalMul H
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathMul H p q)) :=
  rfl

/-- The left native unit homotopy evaluated along a based loop. -/
noncomputable def pathMulReflLeftHomotopy (p : Path H.e H.e) :
    Path.Homotopy (pathMul H (Path.refl H.e) p) p where
  toFun st := H.left_unit (st.1, p st.2)
  continuous_toFun := H.left_unit.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left t := by
    change H.left_unit (0, p t) = pathMul H (Path.refl H.e) p t
    rw [H.left_unit.apply_zero, pathMul_apply,
      hspaceLeftUnitMap_apply]
    rfl
  map_one_left t := by
    exact H.left_unit.apply_one (p t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · change H.left_unit (s, p 0) = pathMul H (Path.refl H.e) p 0
      rw [p.source]
      exact (H.left_unit.eq_snd s (Set.mem_singleton H.e)).trans
        (pathMul H (Path.refl H.e) p).source.symm
    · change H.left_unit (s, p 1) = pathMul H (Path.refl H.e) p 1
      rw [p.target]
      exact (H.left_unit.eq_snd s (Set.mem_singleton H.e)).trans
        (pathMul H (Path.refl H.e) p).target.symm

/-- The right native unit homotopy evaluated along a based loop. -/
noncomputable def pathMulReflRightHomotopy (p : Path H.e H.e) :
    Path.Homotopy (pathMul H p (Path.refl H.e)) p where
  toFun st := H.right_unit (st.1, p st.2)
  continuous_toFun := H.right_unit.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left t := by
    change H.right_unit (0, p t) = pathMul H p (Path.refl H.e) t
    rw [H.right_unit.apply_zero, pathMul_apply,
      hspaceRightUnitMap_apply]
    rfl
  map_one_left t := by
    exact H.right_unit.apply_one (p t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · change H.right_unit (s, p 0) = pathMul H p (Path.refl H.e) 0
      rw [p.source]
      exact (H.right_unit.eq_snd s (Set.mem_singleton H.e)).trans
        (pathMul H p (Path.refl H.e)).source.symm
    · change H.right_unit (s, p 1) = pathMul H p (Path.refl H.e) 1
      rw [p.target]
      exact (H.right_unit.eq_snd s (Set.mem_singleton H.e)).trans
        (pathMul H p (Path.refl H.e)).target.symm

@[simp]
theorem fundamentalMul_one_left (p : FundamentalGroup X H.e) :
    fundamentalMul H 1 p = p := by
  rcases p with ⟨p⟩
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      apply End.ext
      change Path.Homotopic.Quotient.mk (pathMul H (Path.refl H.e) p) =
        Path.Homotopic.Quotient.mk p
      exact Path.Homotopic.Quotient.eq.mpr ⟨pathMulReflLeftHomotopy H p⟩

@[simp]
theorem fundamentalMul_one_right (p : FundamentalGroup X H.e) :
    fundamentalMul H p 1 = p := by
  rcases p with ⟨p⟩
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      apply End.ext
      change Path.Homotopic.Quotient.mk (pathMul H p (Path.refl H.e)) =
        Path.Homotopic.Quotient.mk p
      exact Path.Homotopic.Quotient.eq.mpr ⟨pathMulReflRightHomotopy H p⟩

/-- Pointwise native multiplication commutes strictly with path
concatenation. -/
theorem pathMul_trans
    (p₀ p₁ q₀ q₁ : Path H.e H.e) :
    pathMul H (p₀.trans p₁) (q₀.trans q₁) =
      (pathMul H p₀ q₀).trans (pathMul H p₁ q₁) := by
  ext t
  simp only [pathMul_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- Quotient-level interchange in path-concatenation order. -/
theorem fundamentalMul_trans
    (p₀ p₁ q₀ q₁ : FundamentalGroup X H.e) :
    fundamentalMul H
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans p₀.asHom p₁.asHom))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans q₀.asHom q₁.asHom)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans
        (fundamentalMul H p₀ q₀).asHom
        (fundamentalMul H p₁ q₁).asHom) := by
  rcases p₀ with ⟨p₀⟩
  rcases p₁ with ⟨p₁⟩
  rcases q₀ with ⟨q₀⟩
  rcases q₁ with ⟨q₁⟩
  induction p₀ using Path.Homotopic.Quotient.ind with
  | mk p₀ =>
    induction p₁ using Path.Homotopic.Quotient.ind with
    | mk p₁ =>
      induction q₀ using Path.Homotopic.Quotient.ind with
      | mk q₀ =>
        induction q₁ using Path.Homotopic.Quotient.ind with
        | mk q₁ =>
          apply End.ext
          change Path.Homotopic.Quotient.mk
              (pathMul H (p₀.trans p₁) (q₀.trans q₁)) =
            Path.Homotopic.Quotient.mk
              ((pathMul H p₀ q₀).trans (pathMul H p₁ q₁))
          exact congrArg Path.Homotopic.Quotient.mk
            (pathMul_trans H p₀ p₁ q₀ q₁)

/-- Eckmann--Hilton interchange between the existing fundamental-group
product and native pointwise multiplication. -/
theorem fundamentalMul_interchange
    (a b c d : FundamentalGroup X H.e) :
    fundamentalMul H (a * b) (c * d) =
      fundamentalMul H a c * fundamentalMul H b d := by
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def,
    FundamentalGroup.mul_def]
  exact fundamentalMul_trans H b a d c

/-- Native pointwise multiplication is unital on the fundamental group. -/
theorem fundamentalMul_isUnital :
    EckmannHilton.IsUnital
      (fun p q : FundamentalGroup X H.e ↦ fundamentalMul H p q) 1 :=
  EckmannHilton.IsUnital.mk
    { left_id := fundamentalMul_one_left H
      right_id := fundamentalMul_one_right H }

/-- Named commutative-group structure on the fundamental group at the
native H-space unit.  It is deliberately not a global instance. -/
@[instance_reducible]
noncomputable def fundamentalGroupCommGroup :
    CommGroup (FundamentalGroup X H.e) :=
  EckmannHilton.commGroup (fundamentalMul_isUnital H)
    (fundamentalMul_interchange H)

/-- Fundamental-group multiplication at the distinguished unit is
commutative. -/
theorem fundamentalGroup_mul_comm
    (p q : FundamentalGroup X H.e) : p * q = q * p := by
  let _ : CommGroup (FundamentalGroup X H.e) :=
    fundamentalGroupCommGroup H
  exact mul_comm p q

end HSpaceData
end CGWH

end
