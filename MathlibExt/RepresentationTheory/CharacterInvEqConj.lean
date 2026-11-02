/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Character values at inverses are complex conjugates

For a finite group `G` and a finite-dimensional complex representation `ρ`,
the character at `g⁻¹` is the complex conjugate of the character at `g`:
`χ_ρ(g⁻¹) = conj (χ_ρ g)`. The same holds for the character of the dual
representation: `χ_{ρ.dual} g = conj (χ_ρ g)`.

Proof idea: `ρ g` has finite order, hence is diagonalizable over `ℂ`
(it is semisimple, since it is annihilated by the separable polynomial
`X ^ |G| - 1`). Its eigenvalues are `|G|`-th roots of unity, so they lie on
the unit circle, where complex conjugation is inversion. The trace is the sum
of the eigenvalues (counted with multiplicity, via the eigenspace
decomposition), and `ρ g⁻¹` acts on each eigenspace by the inverse
eigenvalue.

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (theorems
`CharacterTheory.char_inv_eq_conj` and `CharacterTheory.char_dual_eq_conj`).
Mathlib has only the dual case without conjugation,
`Representation.char_dual : ρ.dual.character g = ρ.character g⁻¹`; the
conjugation statement is new. This complements
`CharacterTheory.irreducible_iff_classInnerProduct_self_eq_one` (Batch 10)
and `CharacterTheory.irred_dim_dvd_card` (Batch 7), the other
character-theoretic theorems from the same v1 file.
-/

@[expose] public section

namespace CharacterTheory

universe u

set_option linter.style.haveILetI false in
/-- **Character values at inverses are complex conjugates.** Let $\rho$ be a representation of a
finite group $G$ on a finite-dimensional complex vector space $V$, with character $\chi_\rho$.
For every $g \in G$, $\chi_\rho(g^{-1}) = \overline{\chi_\rho(g)}$. -/
theorem char_inv_eq_conj
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) := by
  classical
  set f : Module.End ℂ V := ρ g
  set f' : Module.End ℂ V := ρ g⁻¹
  have hord : f ^ Fintype.card G = 1 := by
    simp only [f, ← map_pow, pow_card_eq_one, map_one]
  have hfg : f * f' = 1 := by simp only [f, f', ← map_mul, mul_inv_cancel, map_one]
  have hgf : f' * f = 1 := by simp only [f, f', ← map_mul, inv_mul_cancel, map_one]
  have hinj : Function.Injective f :=
    Function.LeftInverse.injective (fun x => LinearMap.congr_fun hgf x)
  have hss : Module.End.IsSemisimple f := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ)
        (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne') one_ne_zero).squarefree
    · simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]; exact sub_eq_zero.mpr hord
  have hint : DirectSum.IsInternal (fun μ : ℂ => f.eigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  have hfin : {μ : ℂ | f.eigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.eigenspaces_iSupIndep
  have hf_maps : ∀ μ : ℂ, Set.MapsTo f (↑(f.eigenspace μ)) (↑(f.eigenspace μ)) := fun μ v hv => by
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv ⊢
    show f (f v) = μ • (f v); rw [hv, map_smul, hv]
  have hg_maps : ∀ μ : ℂ, Set.MapsTo f' (↑(f.eigenspace μ)) (↑(f.eigenspace μ)) := fun μ v hv => by
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv ⊢
    show f (f' v) = μ • (f' v)
    have hfgv : f (f' v) = v := LinearMap.congr_fun hfg v
    have hgfv : f' (f v) = v := LinearMap.congr_fun hgf v
    rw [hv, map_smul] at hgfv; rw [hfgv, hgfv]
  show (LinearMap.trace ℂ V) f' = (starRingEnd ℂ) ((LinearMap.trace ℂ V) f)
  rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hf_maps,
      LinearMap.trace_eq_sum_trace_restrict' hint hfin hg_maps, map_sum]
  congr 1; ext μ
  by_cases hμ_bot : f.eigenspace μ = ⊥
  · have hdim : Module.finrank ℂ (f.eigenspace μ) = 0 := by simp [hμ_bot]
    haveI : Subsingleton (f.eigenspace μ) := Module.finrank_zero_iff.mp hdim
    simp [Subsingleton.elim (f.restrict (hf_maps μ)) 0,
          Subsingleton.elim (f'.restrict (hg_maps μ)) 0]
  · have hμ_ne : μ ≠ 0 := by
      intro hμ0; apply hμ_bot; rw [hμ0, Submodule.eq_bot_iff]; intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv; simp only [zero_smul] at hv
      exact hinj (hv.trans (map_zero f).symm)
    have hμ_pow : μ ^ Fintype.card G = 1 := by
      have hev : Module.End.HasEigenvalue f μ := by
        rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue]; exact hμ_bot
      have hev_mp : (minpoly ℂ f).IsRoot μ := Module.End.hasEigenvalue_iff_isRoot.mp hev
      have hdvd : minpoly ℂ f ∣ (Polynomial.X ^ Fintype.card G - 1) := by
        apply minpoly.dvd; simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]
        exact sub_eq_zero.mpr hord
      have hroot : (Polynomial.X ^ Fintype.card G - 1 : Polynomial ℂ).IsRoot μ := by
        obtain ⟨r, hr⟩ := hdvd; rw [Polynomial.IsRoot.def] at hev_mp ⊢
        rw [hr, Polynomial.eval_mul, hev_mp, zero_mul]
      simpa [Polynomial.IsRoot.def, sub_eq_zero] using hroot
    have hconj : starRingEnd ℂ μ = μ⁻¹ :=
      (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hμ_pow
        (Fintype.card_pos (α := G)).ne')).symm
    have hf_restr : f.restrict (hf_maps μ) = μ • LinearMap.id := by
      ext ⟨v, hv⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      exact Module.End.mem_eigenspace_iff.mp hv
    have hg_restr : f'.restrict (hg_maps μ) = μ⁻¹ • LinearMap.id := by
      ext ⟨v, hv⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      have hev : f v = μ • v := Module.End.mem_eigenspace_iff.mp hv
      have hgfv : f' (f v) = v := LinearMap.congr_fun hgf v
      rw [hev, map_smul] at hgfv
      exact smul_right_injective V hμ_ne
        (hgfv.trans (smul_inv_smul₀ hμ_ne v).symm)
    rw [hf_restr, hg_restr, ← hconj]
    simp [map_smul, LinearMap.trace_id, smul_eq_mul, map_mul, map_natCast]

/-- **Character of the dual representation.** Let $\rho$ be a representation of a finite group
$G$ on a finite-dimensional complex vector space $V$, and let $\rho^*$ be its dual representation.
For every $g \in G$, the character of $\rho^*$ at $g$ is the complex conjugate of the character of
$\rho$ at $g$: $\chi_{\rho^*}(g) = \overline{\chi_\rho(g)}$. -/
theorem char_dual_eq_conj
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.dual.character g = starRingEnd ℂ (ρ.character g) := by
  rw [Representation.char_dual, char_inv_eq_conj]

end CharacterTheory
