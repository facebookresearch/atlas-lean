/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.NativeMappingPath
public import MathlibExt.AlgebraicTopology.ModelCategory.CompatibleFibrationMaps
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalRestriction

/-!
# Strict compatible native maps from actual whole mapping-space paths

Actual consecutive paths with the SAME complete endpoint maps, a literal
restriction formula and a WHOLE mapping-space path homotopy determine
strictly compatible native interval maps. The existing slice-model
extension preserves the entire original boundary and original global
comparison class. It is applied once here; no compatible cocone is given.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

universe u

namespace CGWH

/-- Actual whole consecutive path comparisons construct a strict cocone
of native interval maps, preserving the complete boundary and comparison
class at every original stage. -/
public theorem exists_compatibleMappingPathCocone
    (F : ℕ ⥤ CGWH.{u, u}) [∀ n, T2Space (F.obj n)]
    (M : CGWH.{u, u}) [IsFibrant M]
    (hobjects : ∀ n, IsCofibrant (F.obj n))
    (hcof : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (f g : (n : ℕ) → C(F.obj n, M))
    (p q : (n : ℕ) → Path (f n) (g n))
    (hrestrict : ∀ n t a, q n t a = p (n + 1) t (F.map (homOfLE (Nat.le_succ n)) a))
    (hcompare : ∀ n, (p n).Homotopic (q n)) :
    let E := (ihom nativeInterval.{u, u}).obj M
    let r := (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M
    ∃ c : F ⟶ (Functor.const ℕ).obj E,
      c.app 0 = nativeMappingPathCurry (p 0) ∧
      ∀ n, ∃ h : c.app n ≫ r = nativeMappingPathCurry (p n) ≫ r,
        RightHomotopyRel
          (Over.homMk (U := Over.mk (nativeMappingPathCurry (p n) ≫ r)) (V := Over.mk r)
            (nativeMappingPathCurry (A := F.obj n) (M := M) (p n)) rfl :
            Over.mk (nativeMappingPathCurry (p n) ≫ r) ⟶ Over.mk r)
          (Over.homMk (U := Over.mk (nativeMappingPathCurry (p n) ≫ r)) (V := Over.mk r)
            (c.app n) h) := by
  let E := (ihom nativeInterval.{u, u}).obj M
  let r : E ⟶ (ihom (SSet.toCGWH.{u, u}.obj (∂Δ[1] : SSet.{u}))).obj M :=
    (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M
  let s : (n : ℕ) → F.obj n ⟶ E := fun n => nativeMappingPathCurry (p n)
  let b : (n : ℕ) → F.obj n ⟶
      (ihom (SSet.toCGWH.{u, u}.obj (∂Δ[1] : SSet.{u}))).obj M := fun n => s n ≫ r
  letI : Cofibration (nativeIntervalBoundary.{u, u}) := nativeIntervalBoundary_cofibration.{u, u}
  letI : Fibration r := fibration_pre_app_of_cofibration nativeIntervalBoundary.{u, u}
  have hb : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n := by
    intro n
    have he := nativeMappingPathCurry_precomp (F.map (homOfLE (Nat.le_succ n)))
      (q n) (p (n + 1)) (hrestrict n)
    have hboundary := nativeMappingPathCurry_boundary_eq (p n) (q n)
    calc
      F.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) =
          (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ r :=
        (Category.assoc _ _ _).symm
      _ = nativeMappingPathCurry (q n) ≫ r := congrArg (fun k => k ≫ r) he.symm
      _ = b n := hboundary.symm
  have hOverBoundary : (Over.mk r).hom = r := Over.mk_hom r
  have hOverBase (n : ℕ) : (Over.mk (b n)).hom = b n := Over.mk_hom (b n)
  have hStepFac (n : ℕ) :
      (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ r = b n :=
    (Category.assoc (F.map (homOfLE (Nat.le_succ n))) (s (n + 1)) r).trans (hb n)
  have hStepOver (n : ℕ) :
      (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ (Over.mk r).hom =
        (Over.mk (b n)).hom :=
    (congrArg (fun k : E ⟶
      (ihom (SSet.toCGWH.{u, u}.obj (∂Δ[1] : SSet.{u}))).obj M =>
        (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ k) hOverBoundary).trans
      ((hStepFac n).trans (hOverBase n).symm)
  have hstep : ∀ n, LeftHomotopyRel
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk r)
        (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1))
        (hStepOver n) : Over.mk (b n) ⟶ Over.mk r)
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk r) (s n) rfl) := by
    intro n
    letI : IsCofibrant (F.obj n) := hobjects n
    have he := nativeMappingPathCurry_precomp (F.map (homOfLE (Nat.le_succ n)))
      (q n) (p (n + 1)) (hrestrict n)
    have hboundary := nativeMappingPathCurry_boundary_eq (p n) (q n)
    have hc := nativeMappingPathCurry_leftHomotopyRel_over_of_base
      (q n) (p n) (hcompare n).symm (b n) hboundary.symm rfl
    have hi :
        (Over.homMk (U := Over.mk (b n)) (V := Over.mk r)
          (nativeMappingPathCurry (A := F.obj n) (M := M) (q n)) hboundary.symm :
          Over.mk (b n) ⟶ Over.mk r) =
        Over.homMk (U := Over.mk (b n)) (V := Over.mk r)
        (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1))
          (hStepOver n) := by
      apply Over.OverMorphism.ext
      exact he
    rw [hi] at hc
    exact hc
  exact exists_fibration_cocone_of_successor_homotopies F r b s (fun _ => rfl)
    hobjects hcof hb hstep

end CGWH

end
