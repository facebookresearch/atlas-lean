/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CompactOpenPathHomotopy
public import MathlibExt.Topology.Category.CGWH.NativeIntervalSquare
public import MathlibExt.AlgebraicTopology.ModelCategory.SectionHomotopyExtension
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# Whole original mapping-space paths in the native interval internal Hom

The derived compact-parameter evaluation converts a WHOLE path to its
original native homotopy map. Both endpoint maps determine restriction
along the entire original boundary. One original path homotopy then gives
a homotopy in the actual slice model category, retaining the complete
active source and fixed base; no pointwise filling inference is used.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

universe u

namespace CGWH

local instance overMkLeftT2Space {X Z : CGWH.{u, u}} [T2Space X]
    (b : X ⟶ Z) : T2Space (Over.mk b).left :=
  Eq.mp (congrArg (fun Y : CGWH.{u, u} => T2Space Y) (Over.mk_left b).symm)
    (inferInstance : T2Space X)

variable {A M : CGWH.{u, u}} [T2Space A] {f g : C(A, M)}

private def nativeMappingPathEvaluation (p : Path f g) : nativeInterval.{u, u} ⊗ A ⟶ M :=
  ConcreteCategory.ofHom ((compactOpenPathEvaluation p).comp
    ((nativeIntervalClock.{u, u}.comp (ConcreteCategory.hom (C := CGWH.{u, u})
      (CartesianMonoidalCategory.fst nativeInterval.{u, u} A))).prodMk
        (ConcreteCategory.hom (C := CGWH.{u, u})
          (CartesianMonoidalCategory.snd nativeInterval.{u, u} A))))

private theorem nativeMappingPathEvaluation_apply (p : Path f g)
    (s : nativeInterval.{u, u}) (a : A) :
    nativeMappingPathEvaluation p (tensorMk s a) = p (nativeIntervalClock.{u, u} s) a := by
  change compactOpenPathEvaluation p
    (nativeIntervalClock.{u, u} (CartesianMonoidalCategory.fst nativeInterval.{u, u} A (tensorMk s a)),
      CartesianMonoidalCategory.snd nativeInterval.{u, u} A (tensorMk s a)) = _
  rw [tensorMk_fst, tensorMk_snd]
  exact compactOpenPathEvaluation_apply p (nativeIntervalClock.{u, u} s) a

/-- The ORIGINAL whole path as an actual native interval-homotopy map. -/
public def nativeMappingPathCurry (p : Path f g) : A ⟶ (ihom nativeInterval.{u, u}).obj M :=
  MonoidalClosed.curry (nativeMappingPathEvaluation p)

private theorem nativeMappingPathCurry_uncurry_apply_computed (p : Path f g)
    (s : nativeInterval.{u, u}) (a : A) :
    MonoidalClosed.uncurry (nativeMappingPathCurry p) (tensorMk s a) =
      p (nativeIntervalClock.{u, u} s) a := by
  unfold nativeMappingPathCurry
  exact (ConcreteCategory.congr_hom (MonoidalClosed.uncurry_curry (nativeMappingPathEvaluation p))
      (tensorMk s a)).trans (nativeMappingPathEvaluation_apply p s a)

/-- Every original clock and active-source value is preserved by native currying. -/
public theorem nativeMappingPathCurry_uncurry_apply (p : Path f g)
    (s : nativeInterval.{u, u}) (a : A) :
    MonoidalClosed.uncurry (nativeMappingPathCurry p) (tensorMk s a) =
      p (nativeIntervalClock.{u, u} s) a :=
  nativeMappingPathCurry_uncurry_apply_computed p s a

/-- Whole equality of original path values gives equality of the actual
native interval maps, with no equality of endpoint witnesses required. -/
public theorem nativeMappingPathCurry_congr
    {f' g' : C(A, M)} (p : Path f g) (q : Path f' g')
    (hpq : ∀ s a, p s a = q s a) : nativeMappingPathCurry p = nativeMappingPathCurry q := by
  apply MonoidalClosed.uncurry_injective
  apply ConcreteCategory.hom_ext
  intro z
  have hz := tensorMk_fst_snd z
  rw [← hz, nativeMappingPathCurry_uncurry_apply, nativeMappingPathCurry_uncurry_apply]
  exact hpq _ _

/-- The actual native source map restricts a whole path by its ORIGINAL
value, and native currying retains that exact entire restriction. -/
public theorem nativeMappingPathCurry_precomp
    {B : CGWH.{u, u}} [T2Space B] {h k : C(B, M)} (i : A ⟶ B)
    (p : Path f g) (q : Path h k) (hpq : ∀ s a, p s a = q s (i a)) :
    nativeMappingPathCurry p = i ≫ nativeMappingPathCurry q := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  apply ConcreteCategory.hom_ext
  intro z
  have hz := tensorMk_fst_snd z
  rw [← hz, nativeMappingPathCurry_uncurry_apply, ConcreteCategory.comp_apply,
    tensorMk_whiskerLeft, nativeMappingPathCurry_uncurry_apply]
  exact hpq _ _

/-- Two whole paths with the SAME original endpoints have the SAME
restriction on the ENTIRE actual native interval boundary. -/
public theorem nativeMappingPathCurry_boundary_eq (p q : Path f g) :
    nativeMappingPathCurry p ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M =
      nativeMappingPathCurry q ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M := by
  apply nativeIntervalBoundary_pre_ext.{u, u} (nativeMappingPathCurry p) (nativeMappingPathCurry q)
  all_goals
    apply ConcreteCategory.hom_ext
    intro z
    have hz := tensorMk_fst_snd z
    rw [← hz, ConcreteCategory.comp_apply, tensorMk_whiskerRight,
      nativeMappingPathCurry_uncurry_apply, ConcreteCategory.comp_apply,
      tensorMk_whiskerRight, nativeMappingPathCurry_uncurry_apply]
  · simp only [nativeIntervalClock_zero.{u, u}]
    exact (congrArg (fun q : C(A, M) => q _) p.source).trans
      (congrArg (fun q : C(A, M) => q _) q.source).symm
  · simp only [nativeIntervalClock_one.{u, u}]
    exact (congrArg (fun q : C(A, M) => q _) p.target).trans
      (congrArg (fun q : C(A, M) => q _) q.target).symm

/-- One WHOLE original mapping-space homotopy gives a homotopy in the
actual slice over the full interval boundary. The cylinder, complete
source map and fixed-base equation are all constructed from that square. -/
private theorem nativeMappingPathCurry_over_homotopy
    [IsCofibrant A] (p q : Path f g) (hpq : p.Homotopic q)
    (b : A ⟶ (ihom (SSet.toCGWH.{u, u}.obj (∂Δ[1] : SSet.{u}))).obj M)
    (hp : nativeMappingPathCurry p ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M = b)
    (hq : nativeMappingPathCurry q ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M = b) :
    LeftHomotopyRel (Over.homMk (U := Over.mk b)
      (V := Over.mk ((MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M))
      (nativeMappingPathCurry p) hp)
      (Over.homMk (U := Over.mk b)
      (V := Over.mk ((MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M))
      (nativeMappingPathCurry q) hq) := by
  obtain ⟨H⟩ := hpq
  let K := compactOpenPathHomotopyEvaluation H
  let s₀ := nativeMappingPathCurry p
  let s₁ := nativeMappingPathCurry q
  let r := (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M
  have h₀ : ∀ t a, K ((0, t), a) = MonoidalClosed.uncurry s₀
      (tensorMk (nativeIntervalHomeomorph.{u, u}.symm t) a) := by
    intro t a
    rw [nativeMappingPathCurry_uncurry_apply, nativeIntervalClock_symm_apply.{u, u}]
    exact compactOpenPathHomotopyEvaluation_zero H t a
  have h₁ : ∀ t a, K ((1, t), a) = MonoidalClosed.uncurry s₁
      (tensorMk (nativeIntervalHomeomorph.{u, u}.symm t) a) := by
    intro t a
    rw [nativeMappingPathCurry_uncurry_apply, nativeIntervalClock_symm_apply.{u, u}]
    exact compactOpenPathHomotopyEvaluation_one H t a
  have hsource : ∀ t a, K ((t, 0), a) = MonoidalClosed.uncurry s₀
      (tensorMk (nativeIntervalHomeomorph.{u, u}.symm 0) a) := by
    intro t a
    rw [nativeMappingPathCurry_uncurry_apply, nativeIntervalClock_symm_apply.{u, u}]
    exact (compactOpenPathHomotopyEvaluation_source H t a).trans
      (congrArg (fun q : C(A, M) => q a) p.source).symm
  have htarget : ∀ t a, K ((t, 1), a) = MonoidalClosed.uncurry s₀
      (tensorMk (nativeIntervalHomeomorph.{u, u}.symm 1) a) := by
    intro t a
    rw [nativeMappingPathCurry_uncurry_apply, nativeIntervalClock_symm_apply.{u, u}]
    exact (compactOpenPathHomotopyEvaluation_target H t a).trans
      (congrArg (fun q : C(A, M) => q a) p.target).symm
  let P := nativeIntervalCylinder A
  let L : P.LeftHomotopy s₀ s₁ :=
    { h := nativeSquareCurry K
      h₀ := nativeSquareCurry_zero K s₀ h₀
      h₁ := nativeSquareCurry_one K s₁ h₁ }
  have hbase : L.h ≫ r = P.π ≫ b :=
    (nativeSquareCurry_over_boundary K s₀ hsource htarget).trans
      (by rw [hp])
  exact HomotopicalAlgebra.leftHomotopyRel_over_of_cylinder r b s₀ s₁ hp hq P L hbase

/-- One WHOLE original mapping-space homotopy gives a homotopy in the
actual slice over the full interval boundary, based at its original
first native map. The source cylinder and fixed-base equation are derived. -/
public theorem nativeMappingPathCurry_leftHomotopyRel_over
    [IsCofibrant A] (p q : Path f g) (hpq : p.Homotopic q) :
    let r := (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M
    LeftHomotopyRel
      (Over.homMk (U := Over.mk (nativeMappingPathCurry p ≫ r)) (V := Over.mk r)
        (nativeMappingPathCurry (A := A) (M := M) p) rfl :
        Over.mk (nativeMappingPathCurry p ≫ r) ⟶ Over.mk r)
      (Over.homMk (U := Over.mk (nativeMappingPathCurry p ≫ r)) (V := Over.mk r)
        (nativeMappingPathCurry (A := A) (M := M) q)
        (nativeMappingPathCurry_boundary_eq p q).symm) :=
  nativeMappingPathCurry_over_homotopy p q hpq _ rfl
    (nativeMappingPathCurry_boundary_eq p q).symm

/-- The SAME constructed whole homotopy works over any PROVED original
boundary map. This retains its ordinary map equations instead of
silently identifying the two slice objects. -/
public theorem nativeMappingPathCurry_leftHomotopyRel_over_of_base
    [IsCofibrant A] (p q : Path f g) (hpq : p.Homotopic q)
    (b : A ⟶ (ihom (SSet.toCGWH.{u, u}.obj (∂Δ[1] : SSet.{u}))).obj M)
    (hp : nativeMappingPathCurry p ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M = b)
    (hq : nativeMappingPathCurry q ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M = b) :
    LeftHomotopyRel (Over.homMk (U := Over.mk b)
      (V := Over.mk ((MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M))
      (nativeMappingPathCurry (A := A) (M := M) p) hp)
      (Over.homMk (U := Over.mk b)
      (V := Over.mk ((MonoidalClosed.pre nativeIntervalBoundary.{u, u}).app M))
      (nativeMappingPathCurry (A := A) (M := M) q) hq) :=
  nativeMappingPathCurry_over_homotopy p q hpq b hp hq

end CGWH

end
