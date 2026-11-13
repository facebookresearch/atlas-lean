/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Provenance: added by Adam Kiezun in `facebookresearch/atlas-lean` PR #559
(commit `216eb51c8a2c6771f437f6f2177eca10cee084f3`) and adapted from
`MathlibExt/Analysis/InnerProductSpace/CauchyInterlacing.lean` at immutable
atlas-lean commit `18d1aa399b6ebaa8cd9c4a48795b43f6734c3785`. It lives in
this separate module so that this repository's matrix version in
`CauchyInterlacing.lean` stays unchanged. The declarations are unchanged;
the module docstring (proof synopsis, related results, and the
edition-qualified Horn–Johnson locator) is adjusted. The Meta Platforms
notice above is that source file's header, preserved verbatim.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import MathlibExt.Analysis.InnerProductSpace.CourantFischer

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cauchy interlacing for compressions of self-adjoint operators

Let `T` be a self-adjoint operator on a finite-dimensional inner product
space `E` of dimension `n`, with eigenvalues `λ₀ ≥ λ₁ ≥ ⋯ ≥ λ_{n-1}`, and
let `S ⊆ E` be a subspace of codimension one. The **compression** of `T`
to `S` is the operator `P_S ∘ T` restricted to `S`, where `P_S` is the
orthogonal projection onto `S`. If `μ₀ ≥ μ₁ ≥ ⋯ ≥ μ_{n-2}` are the
eigenvalues of the compression, then the eigenvalues interlace:

```
λ₀ ≥ μ₀ ≥ λ₁ ≥ μ₁ ≥ ⋯ ≥ λ_{n-2} ≥ μ_{n-2} ≥ λ_{n-1}.
```

The proof is the classical dimension-counting argument from the
Courant–Fischer min–max principles
(`MathlibExt.Analysis.InnerProductSpace.CourantFischer`): both
inequalities use the min–max pair (`exists_tail_submodule`,
`exists_unit_ge_of_submodule`). For the upper half, min–max for `T`
gives a subspace `W` of `E` of dimension `n - k` whose Rayleigh form
is at most `λₖ`; cutting `W` down to `S` and applying min–max to the
compression traps `μₖ` below `λₖ`. For the lower half, min–max for
the compression gives a subspace of `S`, viewed as a subspace of `E`,
and min–max for `T` at `k + 1` traps `λₖ₊₁` below `μₖ`.

Pinned Mathlib has the eigenvalue API but no Courant–Fischer or interlacing
statement; Courant–Fischer is proved in
`MathlibExt.Analysis.InnerProductSpace.CourantFischer`.
`MathlibExt/Algebra/Polynomial/Interlacing.lean` concerns interlacing of
polynomial roots, a different statement. The neighboring
`CauchyInterlacing.lean` proves `cauchy_interlacing_leading_principal`:
interlacing of a Hermitian matrix with its leading principal submatrix. The
theorem here is the operator-compression analogue: interlacing of the
eigenvalues of `T` with those of its compression to a codimension-one
subspace.

## Main declarations

* `compression` : the compression of an operator to a subspace.
* `compression_isSymmetric` : the compression of a symmetric operator is
  symmetric.
* `compression_rayleigh` : the compression has the same Rayleigh form as
  the original operator on vectors of the subspace.
* `cauchy_interlacing` : the two interlacing inequalities.

Sources: A.-L. Cauchy, "Sur l'équation à l'aide de laquelle on détermine
les inégalités séculaires des mouvements des planètes", 1829; see also
R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed. (2013),
Theorem 4.3.17, the matrix form: in an orthonormal basis of `E` whose first
`n - 1` vectors span `S`, the matrix of the compression is the leading
principal submatrix of the matrix of `T`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.CauchyInterlacing

open Filter Topology
open scoped _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.CourantFischer

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The compression of an operator `T` to a subspace `S`: project `T x`
orthogonally back onto `S`. -/
noncomputable def compression (T : E →ₗ[𝕜] E) (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] : S →ₗ[𝕜] S :=
  (S.orthogonalProjectionOnto : E →L[𝕜] S).toLinearMap ∘ₗ T ∘ₗ S.subtype

omit [FiniteDimensional 𝕜 E] in
/-- The compression acts by projecting the image back onto the subspace. -/
theorem compression_apply (T : E →ₗ[𝕜] E) (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] (y : S) :
    compression T S y = S.orthogonalProjectionOnto (T (y : E)) :=
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- The compression of a symmetric operator is symmetric. -/
theorem compression_isSymmetric {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    (compression T S).IsSymmetric := by
  intro y z
  rw [compression_apply, compression_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, hT,
    ← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

omit [FiniteDimensional 𝕜 E] in
/-- The Rayleigh form of the compression at `y` equals the Rayleigh form
of the original operator at the underlying vector `(y : E)`. -/
theorem compression_rayleigh {T : E →ₗ[𝕜] E}
    (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] (y : S) :
    rayleighForm (compression T S) y = rayleighForm T (y : E) := by
  unfold rayleighForm
  rw [compression_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

omit [FiniteDimensional 𝕜 E] in
/-- A subspace of dimension `m` can be thinned to a subspace of any
smaller dimension. -/
theorem exists_submodule_le_finrank_eq {W : Submodule 𝕜 E} {m : ℕ}
    (h : m ≤ Module.finrank 𝕜 W) :
    ∃ W' : Submodule 𝕜 E, W' ≤ W ∧ Module.finrank 𝕜 W' = m := by
  obtain ⟨s, hs_card, hs_li⟩ :=
    exists_finset_linearIndependent_of_le_finrank (M := ↥W) h
  refine ⟨Submodule.span 𝕜 (Set.range fun x : s => ((x : ↥W) : E)), ?_, ?_⟩
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro x
    exact (x.1).2
  · have hli : LinearIndependent 𝕜 (fun x : s => ((x : ↥W) : E)) :=
      hs_li.map' W.subtype (LinearMap.ker_eq_bot.mpr W.subtype_injective)
    rw [finrank_span_eq_card hli, Fintype.card_coe, hs_card]

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
  (hn : Module.finrank 𝕜 E = n)

/-- **Cauchy interlacing, upper half.** The `k`-th eigenvalue of the
compression to a codimension-one subspace is at most the `k`-th
eigenvalue of the original operator. -/
theorem eigenvalue_compression_le_eigenvalue (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] (hS : Module.finrank 𝕜 S = n - 1)
    {k : ℕ} (hk : k + 1 < n) :
    (compression_isSymmetric hT S).eigenvalues hS ⟨k, by omega⟩ ≤
      hT.eigenvalues hn ⟨k, by omega⟩ := by
  have hk' : k < n := by omega
  -- Min–max for `T` at `k`: a subspace `W` of dimension `n - k` on which
  -- the Rayleigh form is at most `λₖ`.
  obtain ⟨W, hWdim, hWbound, -⟩ := exists_tail_submodule hT hn hk'
  -- Cut `W` down to `S`: the intersection has dimension at least `(n-1) - k`.
  have hdim : (n - 1) - k ≤ Module.finrank 𝕜 ↥(W ⊓ S) := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq W S
    have hle : Module.finrank 𝕜 ↥(W ⊔ S) ≤ n := by
      rw [← hn]
      exact Submodule.finrank_le _
    omega
  obtain ⟨W', hW'le, hW'dim⟩ := exists_submodule_le_finrank_eq (W := W ⊓ S) hdim
  have hW'S : W' ≤ S := hW'le.trans inf_le_right
  -- View `W'` as a subspace of `S` and apply min–max to the compression.
  have hkn : k < n - 1 := by omega
  obtain ⟨y, hyU, hy1, hge⟩ := exists_unit_ge_of_submodule
    (compression_isSymmetric hT S) hS hkn (W'.comap S.subtype)
    (by rw [(Submodule.comapSubtypeEquivOfLe hW'S).finrank_eq]; exact hW'dim)
  have hyW' : (y : E) ∈ W' := Submodule.mem_comap.mp hyU
  have hyW : (y : E) ∈ W := (Submodule.mem_inf.mp (hW'le hyW')).1
  have hynorm : ‖(y : E)‖ = 1 := by simpa using hy1
  calc (compression_isSymmetric hT S).eigenvalues hS ⟨k, by omega⟩
      ≤ rayleighForm (compression T S) y := hge
    _ = rayleighForm T (y : E) := compression_rayleigh S y
    _ ≤ hT.eigenvalues hn ⟨k, by omega⟩ := hWbound _ hyW hynorm

/-- **Cauchy interlacing, lower half.** The `k`-th eigenvalue of the
compression to a codimension-one subspace is at least the `(k+1)`-st
eigenvalue of the original operator. -/
theorem eigenvalue_le_eigenvalue_compression (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] (hS : Module.finrank 𝕜 S = n - 1)
    {k : ℕ} (hk : k + 1 < n) :
    hT.eigenvalues hn ⟨k + 1, hk⟩ ≤
      (compression_isSymmetric hT S).eigenvalues hS ⟨k, by omega⟩ := by
  -- Min–max for the compression at `k`: a subspace `W` of `S` of
  -- dimension `(n - 1) - k` on which the Rayleigh form is at most `μₖ`.
  have hkn : k < n - 1 := by omega
  obtain ⟨W, hWdim, hWbound, -⟩ := exists_tail_submodule
    (compression_isSymmetric hT S) hS hkn
  -- View `W` as a subspace of `E` and apply min–max to `T` at `k + 1`.
  obtain ⟨x, hxE, hx1, hge⟩ := exists_unit_ge_of_submodule hT hn hk
    (W.map S.subtype)
    (by rw [Submodule.finrank_map_subtype_eq]; omega)
  obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.mp hxE
  have hynormE : ‖(y : E)‖ = 1 := by
    rw [show (y : E) = x from hyx]
    exact hx1
  have hynorm : ‖y‖ = 1 := by simpa using hynormE
  calc hT.eigenvalues hn ⟨k + 1, hk⟩
      ≤ rayleighForm T x := hge
    _ = rayleighForm (compression T S) y := by
        rw [← hyx]
        exact (compression_rayleigh S y).symm
    _ ≤ (compression_isSymmetric hT S).eigenvalues hS ⟨k, by omega⟩ :=
        hWbound _ hyW hynorm

/-- **Cauchy interlacing.** For a codimension-one subspace `S`, the
eigenvalues `μₖ` of the compression of a self-adjoint operator `T`
interlace the eigenvalues `λₖ` of `T`:
`λₖ₊₁ ≤ μₖ ≤ λₖ`. -/
theorem cauchy_interlacing (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    (hS : Module.finrank 𝕜 S = n - 1) {k : ℕ} (hk : k + 1 < n) :
    hT.eigenvalues hn ⟨k + 1, hk⟩ ≤
        (compression_isSymmetric hT S).eigenvalues hS ⟨k, by omega⟩ ∧
      (compression_isSymmetric hT S).eigenvalues hS ⟨k, by omega⟩ ≤
        hT.eigenvalues hn ⟨k, by omega⟩ :=
  ⟨eigenvalue_le_eigenvalue_compression hT hn S hS hk,
    eigenvalue_compression_le_eigenvalue hT hn S hS hk⟩

end MathlibExt.Analysis.InnerProductSpace.CauchyInterlacing
