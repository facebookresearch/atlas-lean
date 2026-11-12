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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Topology.VectorBundle.Riemannian

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 472

open scoped Manifold

/-!
# Matrix representation of Riemannian metrics in coordinate charts

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)

## References

* https://en.wikipedia.org/wiki/Riemannian_manifold (for `metricInChart`)
-/

namespace MetaMathlibExt

-- Analysis 472: Matrix representation of Riemannian metrics in coordinate charts

/-- Given a Riemannian manifold (M,g), we define the matrix representation of g in a coordinate
chart x=(xⁱ) by gᵢⱼ(x)=⟨ ∂ᵢ,∂ⱼ⟩.
-/
noncomputable def metricInChart {M : Type*} [TopologicalSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : ℕ∞) M]
    [hB : Bundle.RiemannianBundle fun (x : M) => TangentSpace (𝓡 n) x]
    (e : PartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    let p := e.symm x
    let di := mfderiv (𝓡 n) (𝓡 n) e.symm x (EuclideanSpace.single i 1)
    let dj := mfderiv (𝓡 n) (𝓡 n) e.symm x (EuclideanSpace.single j 1)
    hB.g.inner p di dj

end MetaMathlibExt

end
