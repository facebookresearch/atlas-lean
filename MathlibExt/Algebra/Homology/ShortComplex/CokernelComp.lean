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
# Cokernels of a composable pair

In an abelian category C, composable maps X —f→ Y —g→ Z give the exact
cokernel sequence Coker(f) → Coker(g∘f) → Coker(g).
The first map is induced by g and the second by the identity of Z;
their projection equations are a∘π_f=π_gf∘g and b∘π_gf=π_g.
The second map is always epic. If g is monic, the first map is monic
and the sequence is short exact.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Let C be abelian and f:X → Y, g:Y → Z composable morphisms.
Write π_f,π_gf,π_g for the respective cokernel projections.

The short complex Coker(f) —a→ Coker(g∘f) —b→ Coker(g),
where a is induced by g and b by the identity of Z. -/
@[reducible]
noncomputable def cokernelCompSequence : ShortComplex C :=
  (kernelCokernelCompSequence f g).sc
    (kernelCokernelCompSequence_exact f g).toIsComplex 3

/-- Let C be abelian and f:X → Y, g:Y → Z composable morphisms.
Write π_f,π_gf,π_g for the respective cokernel projections.

The sequence Coker(f) → Coker(g∘f) → Coker(g) is exact at its middle term. -/
theorem cokernelCompSequence_exact :
    (cokernelCompSequence f g).Exact :=
  (kernelCokernelCompSequence_exact f g).exact 3

/-- Let C be abelian and f:X → Y, g:Y → Z composable morphisms.
Write π_f,π_gf,π_g for the respective cokernel projections.

The final quotient map Coker(g∘f) → Coker(g) is an epimorphism. -/
instance cokernelCompSequence_epi : Epi (cokernelCompSequence f g).g :=
  inferInstanceAs (Epi ((kernelCokernelCompSequence f g).map' 4 5))

/-- Let C be abelian and f:X → Y, g:Y → Z composable morphisms.
Write π_f,π_gf,π_g for the respective cokernel projections.

If g is a monomorphism, the induced map Coker(f) → Coker(g∘f) is a monomorphism. -/
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

/-- Let C be abelian and f:X → Y, g:Y → Z composable morphisms.
Write π_f,π_gf,π_g for the respective cokernel projections.

If g is monic, 0 → Coker(f) → Coker(g∘f) → Coker(g) → 0 is short exact. -/
theorem cokernelCompSequence_shortExact [Mono g] :
    (cokernelCompSequence f g).ShortExact :=
  ShortExact.mk' (cokernelCompSequence_exact f g) inferInstance inferInstance

end CategoryTheory.ShortComplex
