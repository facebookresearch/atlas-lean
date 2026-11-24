/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.EckmannHilton

/-!
# The fundamental group of an H-space

The fundamental group of an H-space at its distinguished unit is abelian.
The proof puts pointwise H-space multiplication on based path-homotopy
classes and applies the Eckmann--Hilton argument against path concatenation.

The resulting commutative-group structure is named rather than installed as
a global instance, avoiding a typeclass diamond with the existing group
structure on `FundamentalGroup`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open unitInterval

universe u

namespace HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Pointwise H-space multiplication of two loops at the H-space unit. -/
noncomputable def pathMul
    (p q : Path (HSpace.e : X) HSpace.e) :
    Path (HSpace.e : X) HSpace.e where
  toFun t := HSpace.hmul (p t, q t)
  continuous_toFun := HSpace.hmul.continuous.comp
    (p.continuous.prodMk q.continuous)
  source' := by rw [p.source, q.source, HSpace.hmul_e_e]
  target' := by rw [p.target, q.target, HSpace.hmul_e_e]

@[simp]
theorem pathMul_apply
    (p q : Path (HSpace.e : X) HSpace.e) (t : unitInterval) :
    pathMul p q t = HSpace.hmul (p t, q t) :=
  rfl

/-- Pointwise multiplication of two path homotopies. -/
noncomputable def pathMulHomotopy
    {p₀ p₁ q₀ q₁ : Path (HSpace.e : X) HSpace.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁) :
    Path.Homotopy (pathMul p₀ q₀) (pathMul p₁ q₁) where
  toFun st := HSpace.hmul (P st, Q st)
  continuous_toFun := HSpace.hmul.continuous.comp
    (P.continuous.prodMk Q.continuous)
  map_zero_left t := by
    rw [P.apply_zero, Q.apply_zero]
    rfl
  map_one_left t := by
    rw [P.apply_one, Q.apply_one]
    rfl
  prop' s t ht := by
    rcases ht with rfl | rfl
    · change HSpace.hmul (P (s, 0), Q (s, 0)) =
        (pathMul p₀ q₀) 0
      rw [P.source, Q.source, HSpace.hmul_e_e]
      exact (pathMul p₀ q₀).source.symm
    · change HSpace.hmul (P (s, 1), Q (s, 1)) =
        (pathMul p₀ q₀) 1
      rw [P.target, Q.target, HSpace.hmul_e_e]
      exact (pathMul p₀ q₀).target.symm

/-- Pointwise H-space multiplication descended to based path-homotopy
classes. -/
noncomputable def fundamentalMul
    (p q : FundamentalGroup X HSpace.e) :
    FundamentalGroup X HSpace.e :=
  FundamentalGroup.fromPath (Quotient.map₂ pathMul
    (fun _ _ hp _ _ hq ↦
      Nonempty.map2 pathMulHomotopy hp hq) p.asHom q.asHom)

@[simp]
theorem fundamentalMul_mk
    (p q : Path (HSpace.e : X) HSpace.e) :
    fundamentalMul
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathMul p q)) :=
  rfl

/-- The left H-space unit homotopy evaluated along a based loop. -/
noncomputable def pathMulReflLeftHomotopy
    (p : Path (HSpace.e : X) HSpace.e) :
    Path.Homotopy (pathMul (Path.refl HSpace.e) p) p where
  toFun st := HSpace.eHmul (st.1, p st.2)
  continuous_toFun := HSpace.eHmul.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left t := by
    change HSpace.eHmul (0, p t) = _
    rw [HSpace.eHmul.apply_zero]
    rfl
  map_one_left t := by
    change HSpace.eHmul (1, p t) = p t
    exact HSpace.eHmul.apply_one (p t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · simpa [pathMul] using HSpace.eHmul.eq_fst s
        (Set.mem_singleton (HSpace.e : X))
    · simpa [pathMul] using HSpace.eHmul.eq_fst s
        (Set.mem_singleton (HSpace.e : X))

/-- The right H-space unit homotopy evaluated along a based loop. -/
noncomputable def pathMulReflRightHomotopy
    (p : Path (HSpace.e : X) HSpace.e) :
    Path.Homotopy (pathMul p (Path.refl HSpace.e)) p where
  toFun st := HSpace.hmulE (st.1, p st.2)
  continuous_toFun := HSpace.hmulE.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left t := by
    change HSpace.hmulE (0, p t) = _
    rw [HSpace.hmulE.apply_zero]
    rfl
  map_one_left t := by
    change HSpace.hmulE (1, p t) = p t
    exact HSpace.hmulE.apply_one (p t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · simpa [pathMul] using HSpace.hmulE.eq_fst s
        (Set.mem_singleton (HSpace.e : X))
    · simpa [pathMul] using HSpace.hmulE.eq_fst s
        (Set.mem_singleton (HSpace.e : X))

@[simp]
theorem fundamentalMul_one_left
    (p : FundamentalGroup X HSpace.e) :
    fundamentalMul 1 p = p := by
  rcases p with ⟨p⟩
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      apply CategoryTheory.End.ext
      change Path.Homotopic.Quotient.mk (pathMul (Path.refl HSpace.e) p) =
        Path.Homotopic.Quotient.mk p
      exact Path.Homotopic.Quotient.eq.mpr ⟨pathMulReflLeftHomotopy p⟩

@[simp]
theorem fundamentalMul_one_right
    (p : FundamentalGroup X HSpace.e) :
    fundamentalMul p 1 = p := by
  rcases p with ⟨p⟩
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      apply CategoryTheory.End.ext
      change Path.Homotopic.Quotient.mk (pathMul p (Path.refl HSpace.e)) =
        Path.Homotopic.Quotient.mk p
      exact Path.Homotopic.Quotient.eq.mpr ⟨pathMulReflRightHomotopy p⟩

/-- Pointwise H-space multiplication commutes strictly with path
concatenation. -/
theorem pathMul_trans
    (p₀ p₁ q₀ q₁ : Path (HSpace.e : X) HSpace.e) :
    pathMul (p₀.trans p₁) (q₀.trans q₁) =
      (pathMul p₀ q₀).trans (pathMul p₁ q₁) := by
  ext t
  simp only [pathMul_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- The quotient-level interchange law in concatenation order. -/
theorem fundamentalMul_trans
    (p₀ p₁ q₀ q₁ : FundamentalGroup X HSpace.e) :
    fundamentalMul
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans p₀.asHom p₁.asHom))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans q₀.asHom q₁.asHom)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans
        (fundamentalMul p₀ q₀).asHom
        (fundamentalMul p₁ q₁).asHom) := by
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
          apply CategoryTheory.End.ext
          change Path.Homotopic.Quotient.mk
              (pathMul (p₀.trans p₁) (q₀.trans q₁)) =
            Path.Homotopic.Quotient.mk
              ((pathMul p₀ q₀).trans (pathMul p₁ q₁))
          exact congrArg Path.Homotopic.Quotient.mk
            (pathMul_trans p₀ p₁ q₀ q₁)

/-- Exact Eckmann--Hilton interchange between the existing fundamental-group
product and pointwise H-space multiplication. -/
theorem fundamentalMul_interchange
    (a b c d : FundamentalGroup X HSpace.e) :
    fundamentalMul (a * b) (c * d) =
      fundamentalMul a c * fundamentalMul b d := by
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def,
    FundamentalGroup.mul_def]
  exact fundamentalMul_trans b a d c

/-- Pointwise H-space multiplication is unital on the fundamental group. -/
theorem fundamentalMul_isUnital :
    EckmannHilton.IsUnital
      (fun p q : FundamentalGroup X HSpace.e ↦ fundamentalMul p q) 1 :=
  EckmannHilton.IsUnital.mk
    { left_id := fundamentalMul_one_left
      right_id := fundamentalMul_one_right }

/-- The named commutative-group structure on the fundamental group of an
H-space at its distinguished unit.  It is deliberately not a global
instance. -/
@[instance_reducible]
noncomputable def fundamentalGroupCommGroup :
    CommGroup (FundamentalGroup X HSpace.e) :=
  EckmannHilton.commGroup fundamentalMul_isUnital fundamentalMul_interchange

/-- The fundamental-group multiplication at the distinguished unit of an
H-space is commutative. -/
theorem fundamentalGroup_mul_comm
    (p q : FundamentalGroup X HSpace.e) : p * q = q * p := by
  let _ : CommGroup (FundamentalGroup X HSpace.e) :=
    fundamentalGroupCommGroup
  exact mul_comm p q

/-- Fundamental-group multiplication is commutative at any point of a path-connected H-space. -/
theorem fundamentalGroup_mul_comm_at_point [PathConnectedSpace X] (x : X)
    (a b : FundamentalGroup X x) : a * b = b * a := by
  let p : Path x (HSpace.e : X) := PathConnectedSpace.somePath x HSpace.e
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  apply E.injective
  rw [E.map_mul, E.map_mul]
  exact fundamentalGroup_mul_comm (E a) (E b)

end HSpace

end
