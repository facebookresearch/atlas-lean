/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.AtkinLehnerSlash

@[expose] public section

open UpperHalfPlane

/-- Source consumer with the original binders. -/
private theorem exactSource {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)
    (k₁ k₂ : ℤ) (F G : ℍ → ℂ) :
    ModularForm.alSlash W (k₁ + k₂) (F * G) =
      (q : ℂ) • (ModularForm.alSlash W k₁ F * ModularForm.alSlash W k₂ G) :=
  ModularForm.alSlash_mul W k₁ k₂ F G

/-- A concrete datum at `M = q = 2`, `R = 1`: its determinant is `2`,
so the factor `q` in the product rule is not `1`. -/
example : ((⟨1, rfl, 0, -1, by norm_num⟩ :
    ModularForm.AtkinLehnerDatum 2 2).alGL.det : ℝ) = 2 :=
  ModularForm.AtkinLehnerDatum.val_det_alGL _
