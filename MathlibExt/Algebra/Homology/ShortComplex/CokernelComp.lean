/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
Positions 3–5 of Mathlib's `kernelCokernelCompSequence` exact sequence.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Direct short-complex tail of `kernelCokernelCompSequence` (positions 3–5). -/
@[reducible]
noncomputable def cokernelCompSequence : ShortComplex C :=
  (kernelCokernelCompSequence f g).sc
    (kernelCokernelCompSequence_exact f g).toIsComplex 3

/-- Exactness at position 3, inherited for `cokernelCompSequence`. -/
theorem cokernelCompSequence_exact :
    (cokernelCompSequence f g).Exact :=
  (kernelCokernelCompSequence_exact f g).exact 3

/-- Epi at the tail, inherited from the final map of `kernelCokernelCompSequence`. -/
instance cokernelCompSequence_epi : Epi (cokernelCompSequence f g).g :=
  inferInstanceAs (Epi ((kernelCokernelCompSequence f g).map' 4 5))

/-- When `g` is mono, the first map of the cokernel tail is mono.

If `g` is mono, the connecting map `δ f g` vanishes. For the position-2
short complex `S` of `kernelCokernelCompSequence`, this means `S.f = 0`.
Exactness at position 2 then gives monicity of `S.g`, which is definitionally
the first map of `cokernelCompSequence`. Hence the tail starts with a mono
when `g` is mono. -/
instance cokernelCompSequence_mono [Mono g] :
    Mono (cokernelCompSequence f g).f := by
  have hδ : kernelCokernelCompSequence.δ f g = 0 := by
    rw [kernelCokernelCompSequence.δ_fac,
      CategoryTheory.Limits.kernel.ι_of_mono g]
    simp
  let S := (kernelCokernelCompSequence f g).sc
    (kernelCokernelCompSequence_exact f g).toIsComplex 2
  have hS_exact : S.Exact :=
    (kernelCokernelCompSequence_exact f g).exact 2
  have hS_f_zero : S.f = 0 := hδ
  have hMono : Mono S.g :=
    (S.exact_iff_mono hS_f_zero).mp hS_exact
  exact hMono

/-- When `g` is mono, the cokernel tail is short exact.

This follows from exactness, monicity of the first map when `g` is mono,
and epicness of the last map. -/
theorem cokernelCompSequence_shortExact [Mono g] :
    (cokernelCompSequence f g).ShortExact :=
  ShortExact.mk' (cokernelCompSequence_exact f g) inferInstance inferInstance

end CategoryTheory.ShortComplex
