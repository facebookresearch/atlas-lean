/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Condensed.PerfectoidIntegralVSites
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.Topology.Category.CompHaus.Limits

/-!
# Continuity of compact tests

The inclusion of compact Hausdorff tests over a fixed affine test is continuous from the
coherent topology to the coefficient topology.

Source: Anschuetz--Mann, arXiv:2403.01951v2, Theorems 1.1 and 4.7,
Definitions 2.3--2.4 and 4.2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SolidGlobalCoefficients

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
open MathlibExt.Condensed.PerfectoidIntegralVSites

private theorem compactTests_compatiblePreserving (p : ℕ) [Fact p.Prime]
    (F : VSheaf p) (T : AffineTest p F) :
    CompatiblePreserving (coefficientTopology F) (compactTests T) := by
  constructor
  intro ℱ Z R x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ h
  have h₁ : f₁.1 = f₂.1 := by
    have e := congrArg _root_.Prod.fst h
    change f₁.1 ≫ 𝟙 T = f₂.1 ≫ 𝟙 T at e
    exact (Category.comp_id f₁.1).symm.trans (e.trans (Category.comp_id f₂.1))
  have h₂ : f₁.2 ≫ g₁ = f₂.2 ≫ g₂ := congrArg _root_.Prod.snd h
  let l : X ⟶ (compactTests T).obj (pullback g₁ g₂) :=
    (f₁.1, pullback.lift f₁.2 f₂.2 h₂)
  have hl₁ : l ≫ (compactTests T).map (pullback.fst g₁ g₂) = f₁ := by
    apply CategoryTheory.Prod.hom_ext <;> simp [l, compactTests]
  have hl₂ : l ≫ (compactTests T).map (pullback.snd g₁ g₂) = f₂ := by
    apply CategoryTheory.Prod.hom_ext <;> simp [l, compactTests, h₁]
  have e := hx (pullback.fst g₁ g₂) (pullback.snd g₁ g₂) hg₁ hg₂ pullback.condition
  simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
    ← Functor.map_comp_apply, ← op_comp, hl₁, hl₂] using congrArg (ℱ.obj.map l.op) e

/-- For a prime $p$, a v-sheaf $F$ on affine perfectoid spaces (`VSheaf`) and an affine test $T$
of $F$: the functor $S ↦ (T, S)$ from compact Hausdorff spaces to pairs of an affine test and a
compact Hausdorff space (`compactTests`) is continuous from the coherent topology to the
coefficient topology (`coefficientTopology`). -/
public theorem compactTestContinuity (p : ℕ) [Fact p.Prime]
    (F : VSheaf p) (T : AffineTest p F) :
    (MathlibExt.Condensed.PerfectoidIntegralVSites.compactTests T).IsContinuous
      (coherentTopology CompHaus.{0})
      (MathlibExt.Condensed.PerfectoidIntegralVSites.coefficientTopology F)
    := by
  apply Functor.isContinuous_of_coverPreserving (compactTests_compatiblePreserving p F T)
  constructor
  intro S R hR
  rw [coefficientTopology, GrothendieckTopology.mem_sInf]
  intro J hJ
  exact hJ.2 T S R hR

end WantedExt.AlgebraicGeometry.SolidGlobalCoefficients
