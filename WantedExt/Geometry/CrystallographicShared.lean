/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared crystallographic-group API

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This neutral helper module is shared by the wallpaper-groups and space-groups wanted entries. The definitions are the trusted (non-hole) helpers from leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e, distributed under the Apache License, Version 2.0; unchanged apart from the namespace.
-/
module

public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.CrystallographicShared

/-- Euclidean space in dimension `d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev EuclideanIsom (d : ℕ) := E d ≃ᵃⁱ[ℝ] E d

abbrev AffineGroup (d : ℕ) := E d ≃ᵃ[ℝ] E d

def IsTranslationBy {d : ℕ} (g : EuclideanIsom d) (v : E d) : Prop :=
  ∀ x : E d, g x = x + v

def IsDiscrete {d : ℕ} (G : Subgroup (EuclideanIsom d)) : Prop :=
  ∀ x : E d, ∀ ε > (0 : ℝ),
    {g : EuclideanIsom d | g ∈ G ∧ dist (g x) x ≤ ε}.Finite

structure IsCrystallographicGroup {d : ℕ} (G : Subgroup (EuclideanIsom d)) : Prop where
  discrete : IsDiscrete G
  cocompact : ∃ v : Fin d → E d, LinearIndependent ℝ v ∧
    ∀ i, ∃ g : EuclideanIsom d, g ∈ G ∧ IsTranslationBy g (v i)

def AffinelyEquivalent {d : ℕ} (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  ∃ φ : AffineGroup d,
    {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
    {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

def CrystallographicGroup (d : ℕ) : Type :=
  { G : Subgroup (EuclideanIsom d) // IsCrystallographicGroup G }

noncomputable def crystallographicCount (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (CrystallographicGroup d) |
    ∃ G₀ : CrystallographicGroup d,
      S = {H : CrystallographicGroup d | AffinelyEquivalent G₀.1 H.1}}

end MathlibExt.Geometry.CrystallographicShared
