/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornLocusPolymorphic
public import MathlibExt.Topology.Convenient.StdSimplexHornLocus

/-!
# Realized horn retraction core

For `0 < n` and `k : Fin (n + 1)`, a continuous retraction from `|Δ[n]|` to
`|Λ[n, k]|` via `SimplexCategory.toTopHomeo`, `_root_.hornRetractMap`, and
the inverse of the realized-horn locus homeomorphism, with only the pointwise
left-inverse law after the realized horn inclusion.

No homotopy, filling, anodyne, weak-equivalence, fibration, product, colimit,
or model-category claim.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

/-- Continuous retraction from the realized simplex onto the realized horn. -/
noncomputable def realizedHornRetract (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    ContinuousMap (SSet.toTop.obj (Δ[n] : SSet.{u}))
      (SSet.toTop.obj (SSet.horn.{u} n k)) :=
  (⟨fun x => (_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm x,
      (_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm.continuous⟩ :
    C({t : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        ∃ j, j ≠ k ∧ t.weights j = 0},
      SSet.toTop.obj (SSet.horn.{u} n k))).comp
    ((_root_.hornRetractMap k hn).comp
      ⟨⇑(SimplexCategory.toTopHomeo (SimplexCategory.mk n)),
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous_toFun⟩)

/-- Pointwise left-inverse law after the realized horn inclusion. -/
theorem realizedHornRetract_ι (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : SSet.toTop.obj (SSet.horn.{u} n k)) :
    realizedHornRetract n k hn
      (SSet.toTop.map (SSet.horn.{u} n k).ι x) = x := by
  have hmem_image :
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι x) ∈
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) ''
          Set.range (SSet.toTop.map (SSet.horn.{u} n k).ι) :=
    ⟨SSet.toTop.map (SSet.horn.{u} n k).ι x,
      Set.mem_range.mpr ⟨x, rfl⟩, rfl⟩
  have hmem_locus : ∃ j, j ≠ k ∧
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι x)).weights j = 0 := by
    have hmem : (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι x) ∈
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) ''
          Set.range (SSet.toTop.map (SSet.horn.{u} n k).ι) :=
      hmem_image
    rw [_root_.hornRange_image_eq_locus_u n k hn] at hmem
    simpa using hmem
  have hfix :
      (_root_.hornRetractMap k hn
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          (SSet.toTop.map (SSet.horn.{u} n k).ι x))).val =
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          (SSet.toTop.map (SSet.horn.{u} n k).ι x) :=
    _root_.hornRetractMap_fix k hn _ hmem_locus
  have hIso_val :
      ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn x).val) =
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          (SSet.toTop.map (SSet.horn.{u} n k).ι x) :=
    rfl
  have heq :
      _root_.hornRetractMap k hn
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          (SSet.toTop.map (SSet.horn.{u} n k).ι x)) =
        _root_.realizedHornHomeomorphHornLocus.{u} n k hn x := by
    apply Subtype.ext
    rw [hfix, hIso_val]
  have hinv :
      (_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm
        (_root_.realizedHornHomeomorphHornLocus.{u} n k hn x) = x :=
    Homeomorph.symm_apply_apply _ x
  change (_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm
    (_root_.hornRetractMap k hn
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι x))) = x
  rw [heq]
  exact hinv

end SSet
