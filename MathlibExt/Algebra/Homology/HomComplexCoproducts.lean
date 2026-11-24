/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Cochains out of coproducts

Arbitrary cochains out of a coproduct of integer-indexed cochain complexes are determined by
precomposition with its coproduct injections. The cochains need not commute with differentials.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex.Cochain

universe w v u

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {J : Type w} [HasColimitsOfShape (Discrete J) D]

/-- Cochains of any degree out of a coproduct are determined by precomposition
with the degree-zero cochains of its chosen coproduct injections. -/
theorem ext_of_precomp_sigma_ι
    {K : J → CochainComplex D ℤ} {T : CochainComplex D ℤ} {d : ℤ}
    (x y : Cochain (∐ K) T d)
    (h : ∀ j, (ofHom (Sigma.ι K j)).comp x (zero_add d) =
      (ofHom (Sigma.ι K j)).comp y (zero_add d)) :
    x = y := by
  apply Cochain.ext
  intro p q hpq
  let E := HomologicalComplex.eval D (ComplexShape.up ℤ) p
  apply (cancel_epi (PreservesCoproduct.iso E K).inv).mp
  apply Sigma.hom_ext
  intro j
  simpa only [E, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc,
    HomologicalComplex.eval_map, zero_cochain_comp_v, ofHom_v] using
    congr_v (h j) p q hpq

end CochainComplex.HomComplex.Cochain

end
