/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.HomotopyGroupMap
public import Mathlib.Topology.Connected.PathConnected

/-!
# Actual positive homotopy groups of the original point's path component

Each positive based cube and each whole relative-boundary homotopy lift to
the original point's path component by retaining every actual source value.
Inclusion and that actual quotient lift are inverse. No connectedness of the
whole space, component-product splitting, inverse or point-equality witness
is assumed. The original cube coordinates and group multiplication remain.
-/

noncomputable section

open scoped Topology Topology.Homotopy unitInterval

universe u

namespace HomotopyGroup

variable {X : Type u} [TopologicalSpace X] {x : X}

private theorem originalPositiveCubeOriginBoundary (n : ℕ) :
    (fun _ : Fin (n + 1) => (0 : unitInterval)) ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨0, Or.inl rfl⟩

private def originalPositiveCubeOriginPath (n : ℕ) (t : Fin (n + 1) → unitInterval) :
    Path (fun _ : Fin (n + 1) => (0 : unitInterval)) t where
  toFun u j := Set.Icc.convexComb 0 (t j) u
  continuous_toFun := continuous_pi (fun j => Set.Icc.continuous_convexComb 0 (t j))
  source' := by
    funext j
    exact Set.Icc.convexComb_zero 0 (t j)
  target' := by
    funext j
    exact Set.Icc.convexComb_one 0 (t j)

private theorem originalPositiveCubeValueMemComponent (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (t : (Fin (n + 1) → unitInterval)) : p t ∈ pathComponent x := by
  let z : (Fin (n + 1) → unitInterval) := fun _ => 0
  have hZero : p z = x := GenLoop.boundary p z (originalPositiveCubeOriginBoundary n)
  let path := (originalPositiveCubeOriginPath n t).map p.1.continuous
  exact mem_pathComponent_iff.mpr ⟨path.cast hZero.symm rfl⟩

private def originalPositiveCubeComponentLift (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) :
    GenLoop (Fin (n + 1)) (pathComponent x) ⟨x, mem_pathComponent_self x⟩ :=
  ⟨⟨(fun t => ⟨p t, originalPositiveCubeValueMemComponent n p t⟩),
      p.1.continuous.subtype_mk (fun t => originalPositiveCubeValueMemComponent n p t)⟩,
    fun t ht => Subtype.ext (GenLoop.boundary p t ht)⟩

private theorem originalPositiveHomotopyValueMemComponent (n : ℕ)
    {p q : GenLoop (Fin (n + 1)) X x}
    (H : p.1.HomotopyRel q.1 (Cube.boundary (Fin (n + 1))))
    (u : unitInterval) (t : (Fin (n + 1) → unitInterval)) : H (u, t) ∈ pathComponent x := by
  let z : (Fin (n + 1) → unitInterval) := fun _ => 0
  have hZero : H (u, z) = x :=
    (H.eq_fst u (originalPositiveCubeOriginBoundary n)).trans
      (GenLoop.boundary p z (originalPositiveCubeOriginBoundary n))
  let f : C((Fin (n + 1) → unitInterval), X) :=
    ⟨(fun s => H (u, s)), H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let path := (originalPositiveCubeOriginPath n t).map f.continuous
  exact mem_pathComponent_iff.mpr ⟨path.cast hZero.symm rfl⟩

private def originalPositiveHomotopyComponentLift (n : ℕ)
    {p q : GenLoop (Fin (n + 1)) X x}
    (H : p.1.HomotopyRel q.1 (Cube.boundary (Fin (n + 1)))) :
    (originalPositiveCubeComponentLift n p).1.HomotopyRel
      (originalPositiveCubeComponentLift n q).1 (Cube.boundary (Fin (n + 1))) where
  toHomotopy :=
    { toFun := fun ut => ⟨H ut, originalPositiveHomotopyValueMemComponent n H ut.1 ut.2⟩
      continuous_toFun := H.continuous.subtype_mk
        (fun ut => originalPositiveHomotopyValueMemComponent n H ut.1 ut.2)
      map_zero_left := by
        intro t
        apply Subtype.ext
        exact H.apply_zero t
      map_one_left := by
        intro t
        apply Subtype.ext
        exact H.apply_one t }
  prop' := by
    intro u t ht
    apply Subtype.ext
    exact H.eq_fst u ht

private def originalPositiveComponentClassLift (n : ℕ) :
    Pi (n + 1) X x → Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩ :=
  Quotient.map (originalPositiveCubeComponentLift n)
    (fun _ _ h => by
      rcases h with ⟨H⟩
      exact ⟨originalPositiveHomotopyComponentLift n H⟩)

private def originalPathComponentInclusion (x : X) : C(pathComponent x, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The positive group isomorphism uses actual inclusion and the value-preserving cube lift. -/
public def positivePathComponentInclusionMulEquiv (n : ℕ) (x : X) :
    Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩ ≃* Pi (n + 1) X x where
  toFun := HomotopyGroup.map (originalPathComponentInclusion x)
  invFun := originalPositiveComponentClassLift n
  left_inv a := by
    obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
    rw [HomotopyGroup.map_mk]
    change HomotopyGroup.mk
      (originalPositiveCubeComponentLift n (GenLoop.map (originalPathComponentInclusion x) p)) =
      HomotopyGroup.mk p
    apply congrArg HomotopyGroup.mk
    apply GenLoop.ext
    intro t
    apply Subtype.ext
    rfl
  right_inv a := by
    obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
    change HomotopyGroup.map (originalPathComponentInclusion x)
      (HomotopyGroup.mk (originalPositiveCubeComponentLift n p)) = HomotopyGroup.mk p
    rw [HomotopyGroup.map_mk]
    apply congrArg HomotopyGroup.mk
    apply GenLoop.ext
    intro t
    rfl
  map_mul' a b := HomotopyGroup.map_mul (originalPathComponentInclusion x) a b

private theorem positivePathComponentInclusionApplyComputed (n : ℕ) (x : X)
    (a : Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    positivePathComponentInclusionMulEquiv n x a =
      HomotopyGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X)) a := by
  rfl

/-- Every original positive class maps by the actual path-component inclusion. -/
public theorem positivePathComponentInclusionMulEquiv_apply (n : ℕ) (x : X)
    (a : Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    positivePathComponentInclusionMulEquiv n x a =
      HomotopyGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X)) a :=
  positivePathComponentInclusionApplyComputed n x a

/-- Both actual maps are inverse on every original positive homotopy class. -/
public theorem positivePathComponentInclusionMulEquiv_inverse_laws (n : ℕ) (x : X) :
    (∀ a, (positivePathComponentInclusionMulEquiv n x).symm
      (positivePathComponentInclusionMulEquiv n x a) = a) ∧
    (∀ b, positivePathComponentInclusionMulEquiv n x
      ((positivePathComponentInclusionMulEquiv n x).symm b) = b) :=
  ⟨(positivePathComponentInclusionMulEquiv n x).symm_apply_apply,
    (positivePathComponentInclusionMulEquiv n x).apply_symm_apply⟩

end HomotopyGroup

end
