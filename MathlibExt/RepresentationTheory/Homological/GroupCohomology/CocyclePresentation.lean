/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation.lean`
and
`P2M/Sol/S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

open groupCohomology

/-- **Presentation criterion for multiplicative 1-cocycles.** Let a group `G` act by automorphisms
on an abelian group `M`, let `P` be an additive abelian group with a scalar operation by `G`, and
let `Fn` and `Fn₁` be subgroups of `M` with `Fn` stable under `G`. Let `π : M → P` restrict to a
surjective `G`-equivariant homomorphism from `Fn` onto `P`, with `π x = 0 ↔ x ∈ Fn₁` for
`x ∈ Fn`, so that the kernel of this restriction is `Fn ∩ Fn₁`. If every additive 1-cocycle
`G → P` is a coboundary, then every multiplicative 1-cocycle `f : G → M` with values in `Fn` is a
coboundary up to this kernel: for some `a ∈ Fn`, each `f g / (g • a / a)` lies in `Fn₁`, hence in
`Fn ∩ Fn₁`. -/
public theorem groupCohomology.exists_div_mem_of_isMulCocycle₁_of_presentation
    {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    [AddCommGroup P] [SMul G P]
    (Fn Fn₁ : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn₁))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
    (f : G → M) (hfF : ∀ g, f g ∈ Fn) (hf : IsMulCocycle₁ f) :
    ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn₁ := by
  have hπdiv : ∀ x y, x ∈ Fn → y ∈ Fn → π (x / y) = π x - π y := by
    intro x y hx hy
    have h := hπmul (x / y) y (Fn.div_mem hx hy) hy
    rw [div_mul_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hc : IsCocycle₁ (fun g => π (f g)) := by
    intro g h
    simp only
    rw [hf g h, hπmul _ _ (hstab _ _ (hfF h)) (hfF g), hπsmul _ _ (hfF h)]
  obtain ⟨x, hx⟩ := hP _ hc
  obtain ⟨a, haF, rfl⟩ := hπsurj x
  refine ⟨a, haF, fun g => ?_⟩
  have hga : g • a ∈ Fn := hstab g a haF
  rw [← hπker _ (Fn.div_mem (hfF g) (Fn.div_mem hga haF)),
    hπdiv _ _ (hfF g) (Fn.div_mem hga haF),
    hπdiv _ _ hga haF, hπsmul _ _ haF, hx g, sub_self]
