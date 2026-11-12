/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import MathlibExt.Geometry.Manifold.Riemannian.Chart

@[expose] public section

open Matrix
open scoped Manifold

namespace MathlibExtTest.Geometry.Manifold.Riemannian.Chart

open MetaMathlibExt

-- Analysis 472: Matrix representation of Riemannian metrics in coordinate charts

/-The lemma checks that the matrix g_ij(x) that we build in a chart is symmetric.-/

lemma metricInChart_symm {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : ℕ∞) M]
    [hB : Bundle.RiemannianBundle fun (x : M) => TangentSpace (𝓡 n) x]
    (e : PartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    (metricInChart e x).transpose = metricInChart e x := by
  ext i j
  simp only [metricInChart, transpose_apply, of_apply]
  exact hB.g.symm (e.symm x) _ _

end MathlibExtTest.Geometry.Manifold.Riemannian.Chart

end
