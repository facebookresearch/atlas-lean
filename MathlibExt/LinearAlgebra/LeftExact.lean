/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.LeftExact

@[expose] public section

/-!
# Converse to left-exactness of `Hom`

Mathlib shows that precomposition with an exact pair of linear maps whose second map is
surjective preserves exactness (`LinearMap.exact_lcomp_of_exact_of_surjective`). This module
records the converse: if precomposition yields an exact sequence for every test module,
then the original pair is exact and the second map is surjective.
-/

namespace LinearMap

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type w} [AddCommGroup P] [Module R P]

/-- **Hom detects exact sequences ending in a surjection.** Let $R$ be a commutative ring, let
$M$, $N$, $P$ be $R$-modules, and let $\varphi : M \to N$ and $\psi : N \to P$ be $R$-linear
maps. Then the image of $\varphi$ equals the kernel of $\psi$ and $\psi$ is surjective if and
only if, for every $R$-module $D$ in the same universe as $N$ and $P$, precomposition with $\psi$,
$g \mapsto g \circ \psi$, is an injective map $\operatorname{Hom}_R(P, D) \to
\operatorname{Hom}_R(N, D)$ whose image is the kernel of precomposition with $\varphi$,
$h \mapsto h \circ \varphi$, as a map $\operatorname{Hom}_R(N, D) \to \operatorname{Hom}_R(M, D)$.
-/
theorem exact_and_surjective_iff_forall_lcomp
    (φ : M →ₗ[R] N) (ψ : N →ₗ[R] P) :
    (Function.Exact φ ψ ∧ Function.Surjective ψ) ↔
      ∀ (D : Type w) [AddCommGroup D] [Module R D],
        Function.Injective (lcomp R D ψ) ∧
        Function.Exact (lcomp R D ψ) (lcomp R D φ) := by
  constructor
  · rintro ⟨hex, hsurj⟩ D _ _
    exact ⟨lcomp_injective_of_surjective ψ hsurj,
      exact_lcomp_of_exact_of_surjective (N := D) hex hsurj⟩
  · intro h
    have hker : ker ψ ≤ range φ := by
      intro x hx
      have hexD := (h (N ⧸ range φ)).2
      have hq : (lcomp R (N ⧸ range φ) φ) (range φ).mkQ = 0 :=
        range_mkQ_comp φ
      obtain ⟨θ, hθ⟩ := (hexD (range φ).mkQ).mp hq
      have hqx : (range φ).mkQ x = 0 := by
        have e : θ (ψ x) = (range φ).mkQ x := DFunLike.congr_fun hθ x
        rw [← e, mem_ker.mp hx, map_zero]
      have hmem : x ∈ ker (range φ).mkQ := mem_ker.mpr hqx
      rwa [Submodule.ker_mkQ] at hmem
    have hcomp : ψ ∘ₗ φ = 0 := by
      have hexP := (h P).2
      have hmem : ψ ∈ Set.range (lcomp R P ψ) := ⟨id, by ext x; rfl⟩
      exact (hexP ψ).mpr hmem
    have hsurj : Function.Surjective ψ := by
      rw [← range_eq_top]
      apply range_eq_top_of_cancel
      intro u v huv
      have hinj := (h (P ⧸ range ψ)).1
      exact hinj huv
    exact ⟨exact_iff.mpr (le_antisymm hker (range_le_ker_iff.mpr hcomp)), hsurj⟩

end LinearMap
