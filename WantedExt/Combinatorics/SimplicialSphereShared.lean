/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared finite simplicial sphere API

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This neutral helper module is shared by the Dehn–Sommerville and
upper-bound simplicial-sphere wanted entries, so both theorems speak
about the same sphere type and face-vector API. The definitions are the
trusted (non-hole) helpers from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, modules
`LeanEval.Combinatorics.DehnSommerville` and
`LeanEval.Combinatorics.UpperBoundSimplicialSpheres`, distributed under
the Apache License, Version 2.0; they are unchanged apart from the
namespace.
-/
module

public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.SimplicialSphereShared

/-- A finite geometric simplicial complex homeomorphic to the `(d-1)`-sphere. -/
structure FiniteSimplicialSphere (d : ℕ) where
  K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d))
  finite_faces : K.faces.Finite
  sphere_homeomorph :
    Nonempty (K.space ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)

/-- Number of `k`-dimensional faces (faces with `k+1` vertices). -/
noncomputable def faceCount {d : ℕ} (X : FiniteSimplicialSphere d) (k : ℕ) : ℕ :=
  {s : Finset (EuclideanSpace ℝ (Fin d)) | s ∈ X.K.faces ∧ s.card = k + 1}.ncard

/-- Extended f-vector entry: `f_{-1} = 1`, then `f_{i-1}`. -/
noncomputable def extendedFaceCount {d : ℕ} (X : FiniteSimplicialSphere d) (i : ℕ) : ℕ :=
  if i = 0 then 1 else faceCount X (i - 1)

/-- The h-vector via the alternating binomial transform of the f-vector. -/
noncomputable def hVector {d : ℕ} (X : FiniteSimplicialSphere d) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (j + 1),
    (-1 : ℤ) ^ (j - i) * (Nat.choose (d - i) (j - i) : ℤ) *
      (extendedFaceCount X i : ℤ)

end MathlibExt.Combinatorics.SimplicialSphereShared
