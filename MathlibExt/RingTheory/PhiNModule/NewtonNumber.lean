/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.PhiNModule.Basic
public import MathlibExt.LinearAlgebra.Determinant.Semilinear
public import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear
public import Mathlib.RingTheory.Valuation.Basic

/-!
# The Newton number of a `(φ, N)`-module

Let `K₀` be a field, `σ` a ring automorphism of `K₀` and `v : AddValuation K₀ (WithTop ℤ)` an
additive valuation with `v (σ x) = v x` for all `x`. In the setting of Fontaine–Ouyang,
`K₀ = W(k)[1/p]`, `σ` is the absolute Frobenius and `v = v_p` is the `p`-adic valuation.

Let `D` be a `(φ, N)`-module over `K₀` of finite dimension `r`. The Frobenius `φ` induces a
`σ`-semilinear bijection of the line `⋀^r D`, which in a basis `e` of this line reads
`φ (a • e) = σ a • λ • e` for some `λ ∈ K₀ˣ`; the *Newton number* of `D` is `t_N(D) = v(λ)`. If `b`
is a basis of `D`, then `e = b 0 ∧ ⋯ ∧ b (r - 1)` is a basis of `⋀^r D` and `λ` is the
determinant of the matrix of `φ` in `b`. Another basis multiplies `λ` by `σ u / u` for a unit
`u ∈ K₀`, which does not change `v(λ)` as `v ∘ σ = v`.

## Main definitions

* `PhiNModule.newtonNumber v M`: the Newton number `t_N(D)`, the value under `v` of the
  determinant of the matrix of `φ` in the basis `Module.finBasis K₀ D`, which is an integer as
  this determinant is nonzero.

## Main results

* `Module.Basis.addValuation_det_compₛₗ_eq`: if `v ∘ σ = v`, the value under `v` of the
  determinant of the matrix of a `σ`-semilinear automorphism in a basis does not depend on the
  basis.
* `PhiNModule.coe_newtonNumber`: if `v ∘ σ = v`, the Newton number is the value under `v` of the
  determinant of the matrix of `φ` in any basis of `D`.
* `PhiNModule.newtonNumber_eq_of_linearEquiv`: the Newton number is invariant under linear
  isomorphisms commuting with `φ`.
* `PhiNModule.newtonNumber_eq_add_of_exact` and `PhiNModule.newtonNumber_eq_restrict_add_quotient`:
  the Newton number is additive in short exact sequences.
* `PhiNModule.powMapₛₗ_ιMulti`, `PhiNModule.exists_powMapₛₗ_eq_smul` and
  `PhiNModule.coe_newtonNumber_eq_of_powMapₛₗ`: the description by the top exterior power, where
  `φ` acts on `b 0 ∧ ⋯ ∧ b (r - 1)` by multiplication by the determinant of its matrix in `b`.

## Implementation notes

The definition uses the basis `Module.finBasis K₀ D` for every `v`, and makes sense for every
additive valuation; the results relating it to other bases assume `v (σ x) = v x` for all `x`.
Only the Frobenius enters: the monodromy `N` plays no role, and the invariance and additivity
results only ask the maps to commute with `φ`.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.2, Definitions 8.18 and 8.20, Propositions 8.21 and 8.22 (1).
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.4.1 p. 150.
-/

@[expose] public section

open Module

namespace PhiNModule

variable {K₀ : Type*} [Field K₀] {σ σ' : K₀ →+* K₀} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {p : K₀} {D : Type*} [AddCommGroup D] [Module K₀ D] (v : AddValuation K₀ (WithTop ℤ))

/-! ### Determinants of semilinear automorphisms -/

/-- Change of basis for the valuation of the determinant of a `σ`-semilinear map, for two bases
indexed by the same type. -/
private theorem addValuation_det_compₛₗ_eq_of_index (hv : ∀ x, v (σ x) = v x) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b b' : Basis ι K₀ D) (f : D →ₛₗ[σ] D) :
    v (b.det (f ∘ b)) = v (b'.det (f ∘ b')) := by
  have h := congrArg v (b.det_mul_det_compₛₗ b' f)
  rw [AddValuation.map_mul, AddValuation.map_mul, hv, add_comm] at h
  exact (WithTop.add_right_cancel (v.ne_top_iff.mpr (b.isUnit_det b').ne_zero) h).symm

/-- For a ring automorphism `σ` of `K₀` (with inverse `σ'`), an additive valuation
`v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x` and a `σ`-semilinear
automorphism `f` of `D`, the value under `v` of the determinant `b.det (f ∘ b)` of the matrix of
`f` in a finite basis `b` of `D` is the same for any two finite bases `b` and `b'` of `D`, which
may be indexed by different types. -/
theorem _root_.Module.Basis.addValuation_det_compₛₗ_eq (hv : ∀ x, v (σ x) = v x) {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Basis ι K₀ D)
    (b' : Basis ι' K₀ D) (f : D ≃ₛₗ[σ] D) :
    v (b.det (f ∘ b)) = v (b'.det (f ∘ b')) := by
  let e : ι ≃ ι' := Fintype.equivOfCardEq <| by
    rw [← finrank_eq_card_basis b, ← finrank_eq_card_basis b']
  have h := addValuation_det_compₛₗ_eq_of_index v hv b (b'.reindex e.symm) (f : D →ₛₗ[σ] D)
  rw [LinearEquiv.coe_coe, Basis.coe_reindex, Equiv.symm_symm, ← Function.comp_assoc,
    Basis.det_reindex_symm] at h
  exact h

/-- For a `(φ, N)`-module `M` on `D` and a finite basis `b` of `D`, the determinant
`b.det (M.φ ∘ b)` of the matrix of `φ` in `b` is nonzero. -/
theorem det_comp_φ_ne_zero (M : PhiNModule σ p D) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K₀ D) : b.det (M.φ ∘ b) ≠ 0 :=
  (b.isUnit_det_compₛₗ M.φ).ne_zero

/-! ### The top exterior power -/

/-- An alternating map `F` in `ι`-indexed families, for a finite basis `b` indexed by `ι`, takes
the value `b.det w • F b` at any family `w`. -/
private theorem alternatingMap_apply_eq_det_smul {N : Type*} [AddCommGroup N] [Module K₀ N]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : D [⋀^ι]→ₗ[K₀] N) (b : Basis ι K₀ D)
    (w : ι → D) : F w = b.det w • F b := by
  suffices h : F = b.det.smulRight (F b) by
    conv_lhs => rw [h]
    rfl
  refine b.ext_alternating fun u hu => ?_
  let π : Equiv.Perm ι := Equiv.ofBijective u (Finite.injective_iff_bijective.mp hu)
  have hπ : (fun i => b (u i)) = b ∘ π := rfl
  rw [hπ, F.map_perm, AlternatingMap.map_perm, AlternatingMap.smulRight_apply, Basis.det_self,
    one_smul]

/-- The wedge of the vectors of a basis indexed by `Fin n` is nonzero in `⋀[K₀]^n D`. -/
private theorem ιMulti_basis_ne_zero {n : ℕ} (b : Basis (Fin n) K₀ D) :
    exteriorPower.ιMulti K₀ n b ≠ 0 := by
  intro h
  have h' := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det b
  rw [h, map_zero, Basis.det_self] at h'
  exact zero_ne_one h'

/-- Every element of `⋀[K₀]^n D` is a multiple of the wedge of the vectors of a basis indexed by
`Fin n`. -/
private theorem exists_smul_ιMulti_eq {n : ℕ} (b : Basis (Fin n) K₀ D) (x : ⋀[K₀]^n D) :
    ∃ a : K₀, a • exteriorPower.ιMulti K₀ n b = x := by
  have hx : x ∈ (⊤ : Submodule K₀ (⋀[K₀]^n D)) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span K₀ n D] at hx
  refine Submodule.mem_span_singleton.mp (Submodule.span_le.mpr ?_ hx)
  rintro - ⟨w, rfl⟩
  exact Submodule.mem_span_singleton.mpr
    ⟨b.det w, (alternatingMap_apply_eq_det_smul _ b w).symm⟩

/-- For a `(φ, N)`-module `M` on `D` and a basis `b` of `D` indexed by `Fin r`, where
`r = finrank K₀ D`, the map induced by `φ` on `⋀[K₀]^r D` sends `b 0 ∧ ⋯ ∧ b (r - 1)` to its
multiple by the determinant `b.det (M.φ ∘ b)` of the matrix of `φ` in `b` (Fontaine–Ouyang,
Proposition 8.21). -/
theorem powMapₛₗ_ιMulti (M : PhiNModule σ p D) (b : Basis (Fin (finrank K₀ D)) K₀ D) :
    ExteriorAlgebra.powMapₛₗ (finrank K₀ D) σ (M.φ : D →ₛₗ[σ] D)
        (exteriorPower.ιMulti K₀ (finrank K₀ D) b) =
      b.det (M.φ ∘ b) • exteriorPower.ιMulti K₀ (finrank K₀ D) b := by
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti]
  exact alternatingMap_apply_eq_det_smul _ b _

/-! ### The Newton number -/

variable [FiniteDimensional K₀ D]

/-- The Newton number `t_N(D)` of a finite-dimensional `(φ, N)`-module `M` on `D`, with respect to
an additive valuation `v : AddValuation K₀ (WithTop ℤ)`: the value under `v` of the determinant of
the matrix of `φ` in the basis `Module.finBasis K₀ D`. This determinant is nonzero, so its value
is an integer (`PhiNModule.coe_newtonNumber_finBasis`), and the default value `0` of
`WithTop.untopD` is never used. If `v (σ x) = v x` for all `x`, then any other basis gives the
same value (`PhiNModule.coe_newtonNumber`). -/
noncomputable def newtonNumber (M : PhiNModule σ p D) : ℤ :=
  WithTop.untopD 0 (v ((Module.finBasis K₀ D).det (M.φ ∘ Module.finBasis K₀ D)))

/-- For a finite-dimensional `(φ, N)`-module `M` on `D` and an additive valuation
`v : AddValuation K₀ (WithTop ℤ)`, the Newton number of `M`, viewed in `WithTop ℤ`, is the value
under `v` of the determinant of the matrix of `φ` in the basis `Module.finBasis K₀ D`. -/
theorem coe_newtonNumber_finBasis (M : PhiNModule σ p D) :
    (M.newtonNumber v : WithTop ℤ) = v ((finBasis K₀ D).det (M.φ ∘ finBasis K₀ D)) := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp
    (v.ne_top_iff.mpr (M.det_comp_φ_ne_zero (finBasis K₀ D)))
  rw [newtonNumber, ← ha, WithTop.untopD_coe]

/-- For an additive valuation `v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x`,
a finite-dimensional `(φ, N)`-module `M` on `D` and any finite basis `b` of `D`, the Newton number
of `M`, viewed in `WithTop ℤ`, is the value under `v` of the determinant `b.det (M.φ ∘ b)` of the
matrix of `φ` in `b` (Fontaine–Ouyang, Proposition 8.21). -/
theorem coe_newtonNumber (hv : ∀ x, v (σ x) = v x) (M : PhiNModule σ p D) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι K₀ D) :
    (M.newtonNumber v : WithTop ℤ) = v (b.det (M.φ ∘ b)) := by
  rw [coe_newtonNumber_finBasis, Basis.addValuation_det_compₛₗ_eq v hv _ b]

/-- For any additive valuation `v : AddValuation K₀ (WithTop ℤ)`, the Newton number of a
`(φ, N)`-module `M` on a zero-dimensional space `D` is `0`. -/
theorem newtonNumber_eq_zero_of_finrank_eq_zero (M : PhiNModule σ p D) (hD : finrank K₀ D = 0) :
    M.newtonNumber v = 0 := by
  have : IsEmpty (Fin (finrank K₀ D)) := by
    rw [hD]
    infer_instance
  rw [newtonNumber, Basis.det_apply, Matrix.det_isEmpty, AddValuation.map_one]
  exact WithTop.untopD_coe 0 0

/-- For an additive valuation `v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x`,
two finite-dimensional `(φ, N)`-modules `M₁` on `D₁` and `M₂` on `D₂` have the same Newton number
if there is a `K₀`-linear isomorphism `e : D₁ ≃ D₂` with `e (M₁.φ x) = M₂.φ (e x)` for all `x`
(no compatibility with `N` is needed). -/
theorem newtonNumber_eq_of_linearEquiv (hv : ∀ x, v (σ x) = v x) {D₁ D₂ : Type*}
    [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂] [FiniteDimensional K₀ D₁]
    [FiniteDimensional K₀ D₂] (M₁ : PhiNModule σ p D₁) (M₂ : PhiNModule σ p D₂)
    (e : D₁ ≃ₗ[K₀] D₂) (he : ∀ x, e (M₁.φ x) = M₂.φ (e x)) :
    M₁.newtonNumber v = M₂.newtonNumber v := by
  have h := coe_newtonNumber v hv M₂ ((finBasis K₀ D₁).map e)
  have h' : e.symm ∘ M₂.φ ∘ (finBasis K₀ D₁).map e = M₁.φ ∘ finBasis K₀ D₁ := by
    ext i
    simp only [Function.comp_apply, Basis.map_apply, ← he, LinearEquiv.symm_apply_apply]
  rw [Basis.det_map, h', ← coe_newtonNumber_finBasis] at h
  exact_mod_cast h.symm

/-- Additivity of the Newton number in short exact sequences (Fontaine–Ouyang,
Proposition 8.22 (1)): let `v : AddValuation K₀ (WithTop ℤ)` be an additive valuation with
`v (σ x) = v x` for all `x`, and let `M'`, `M`, `M''` be finite-dimensional `(φ, N)`-modules on
`D'`, `D`, `D''`. If `f : D' → D` and `g : D → D''` are `K₀`-linear maps, with `f` injective, `g`
surjective, the sequence exact at `D`, and `f (M'.φ x) = M.φ (f x)` and
`g (M.φ x) = M''.φ (g x)` for all `x` (no compatibility with `N` is needed), then the Newton number
of `M` is the sum of those of `M'` and `M''`. -/
theorem newtonNumber_eq_add_of_exact (hv : ∀ x, v (σ x) = v x) {D' D'' : Type*}
    [AddCommGroup D'] [Module K₀ D'] [AddCommGroup D''] [Module K₀ D'']
    {M' : PhiNModule σ p D'} {M : PhiNModule σ p D} {M'' : PhiNModule σ p D''}
    [FiniteDimensional K₀ D'] [FiniteDimensional K₀ D''] {f : D' →ₗ[K₀] D} {g : D →ₗ[K₀] D''}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hfφ : ∀ x, f (M'.φ x) = M.φ (f x)) (hgφ : ∀ x, g (M.φ x) = M''.φ (g x)) :
    M.newtonNumber v = M'.newtonNumber v + M''.newtonNumber v := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.mpr hg)
  obtain ⟨e, hef, heg⟩ := hfg.splitSurjectiveEquiv hf ⟨s, hs⟩
  set b' := finBasis K₀ D'
  set b'' := finBasis K₀ D''
  -- the basis of `D` made of the image of `b'` under `f` and a lift of `b''` along `g`
  set B := (b'.prod b'').map e.symm
  have hBl (i) : B (Sum.inl i) = f (b' i) := by
    simp only [B, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl, Sum.elim_inl,
      Function.comp_apply, hef, LinearMap.coe_comp, LinearEquiv.coe_coe]
  have hBr (j) : g (B (Sum.inr j)) = b'' j := by
    simp only [B, heg, Basis.map_apply, Basis.prod_apply, LinearMap.coe_inr, Sum.elim_inr,
      Function.comp_apply, LinearMap.coe_comp, LinearMap.coe_snd, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have he₁ (y) : (e (f y)).1 = y := by
    simp only [hef, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inl,
      Function.comp_apply, LinearEquiv.apply_symm_apply]
  have he₂ (x) : (e x).2 = g x := by
    simp only [heg, LinearMap.coe_comp, LinearMap.coe_snd, LinearEquiv.coe_coe,
      Function.comp_apply]
  have hrepr (x) : B.repr x = (b'.prod b'').repr (e x) := by
    simp only [B, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  -- the matrix of `φ` in `B` is block upper triangular
  have key : B.det (M.φ ∘ B) = b'.det (M'.φ ∘ b') * b''.det (M''.φ ∘ b'') := by
    rw [Basis.det_apply, Basis.det_apply, Basis.det_apply,
      ← Matrix.fromBlocks_toBlocks (B.toMatrix (M.φ ∘ B))]
    have h₂₁ : (B.toMatrix (M.φ ∘ B)).toBlocks₂₁ = 0 := by
      ext i j
      simp only [Matrix.toBlocks₂₁, Basis.toMatrix_apply, Function.comp_apply, hBl, ← hfφ,
        hrepr, Basis.prod_repr_inr, he₂, hfg.apply_apply_eq_zero, map_zero, Finsupp.coe_zero,
        Pi.zero_apply, Matrix.of_apply, Matrix.zero_apply]
    have h₁₁ : (B.toMatrix (M.φ ∘ B)).toBlocks₁₁ = b'.toMatrix (M'.φ ∘ b') := by
      ext i j
      simp only [Matrix.toBlocks₁₁, Basis.toMatrix_apply, Function.comp_apply, hBl, ← hfφ,
        hrepr, Basis.prod_repr_inl, he₁, Matrix.of_apply]
    have h₂₂ : (B.toMatrix (M.φ ∘ B)).toBlocks₂₂ = b''.toMatrix (M''.φ ∘ b'') := by
      ext i j
      simp only [Matrix.toBlocks₂₂, Basis.toMatrix_apply, Function.comp_apply, hrepr,
        Basis.prod_repr_inr, he₂, hgφ, hBr, Matrix.of_apply]
    rw [h₂₁, Matrix.det_fromBlocks_zero₂₁, h₁₁, h₂₂]
  have h := coe_newtonNumber v hv M B
  rw [key, AddValuation.map_mul, ← coe_newtonNumber_finBasis, ← coe_newtonNumber_finBasis] at h
  exact_mod_cast h

/-- Additivity of the Newton number for a stable subspace (Fontaine–Ouyang,
Proposition 8.22 (1)): for an additive valuation `v : AddValuation K₀ (WithTop ℤ)` with
`v (σ x) = v x` for all `x`, a finite-dimensional `(φ, N)`-module `M` on `D` and a subspace `D'`
stable under `φ` and `N`, the Newton number of `M` is the sum of those of the restriction of `M`
to `D'` and of the quotient `D ⧸ D'`. -/
theorem newtonNumber_eq_restrict_add_quotient (hv : ∀ x, v (σ x) = v x) (M : PhiNModule σ p D)
    (D' : Submodule K₀ D) (h : M.IsStable D') :
    M.newtonNumber v = (M.restrict D' h).newtonNumber v + (M.quotient D' h).newtonNumber v :=
  newtonNumber_eq_add_of_exact v hv D'.injective_subtype D'.mkQ_surjective
    (LinearMap.exact_subtype_mkQ D') (fun _ => rfl) (fun _ => rfl)

/-- For a finite-dimensional `(φ, N)`-module `M` on `D`, with `r = finrank K₀ D`, the map induced
by `φ` on `⋀[K₀]^r D` has an eigenvector: a nonzero `e` with image `c • e` for some `c ∈ K₀`
(Fontaine–Ouyang, Definition 8.20). -/
theorem exists_powMapₛₗ_eq_smul (M : PhiNModule σ p D) :
    ∃ e : ⋀[K₀]^(finrank K₀ D) D, e ≠ 0 ∧ ∃ c : K₀,
      ExteriorAlgebra.powMapₛₗ (finrank K₀ D) σ (M.φ : D →ₛₗ[σ] D) e = c • e :=
  ⟨_, ιMulti_basis_ne_zero (finBasis K₀ D), _, M.powMapₛₗ_ιMulti (finBasis K₀ D)⟩

/-- The Newton number via the top exterior power (Fontaine–Ouyang, Definition 8.20): for an
additive valuation `v : AddValuation K₀ (WithTop ℤ)` with `v (σ x) = v x` for all `x` and a
finite-dimensional `(φ, N)`-module `M` on `D`, with `r = finrank K₀ D`, if the map induced by `φ`
on `⋀[K₀]^r D` sends a nonzero `e` to `c • e`, then the Newton number of `M`, viewed in
`WithTop ℤ`, is `v c`. -/
theorem coe_newtonNumber_eq_of_powMapₛₗ (hv : ∀ x, v (σ x) = v x) (M : PhiNModule σ p D)
    {e : ⋀[K₀]^(finrank K₀ D) D} (he : e ≠ 0) {c : K₀}
    (hc : ExteriorAlgebra.powMapₛₗ (finrank K₀ D) σ (M.φ : D →ₛₗ[σ] D) e = c • e) :
    (M.newtonNumber v : WithTop ℤ) = v c := by
  obtain ⟨a, rfl⟩ := exists_smul_ιMulti_eq (finBasis K₀ D) e
  have ha : a ≠ 0 := by
    rintro rfl
    exact he (zero_smul _ _)
  rw [map_smulₛₗ, M.powMapₛₗ_ιMulti, smul_smul, smul_smul] at hc
  have h := congrArg v (smul_left_injective K₀ (ιMulti_basis_ne_zero (finBasis K₀ D)) hc)
  rw [AddValuation.map_mul, AddValuation.map_mul, hv, add_comm (v c)] at h
  rw [coe_newtonNumber_finBasis]
  exact WithTop.add_left_cancel (v.ne_top_iff.mpr ha) h

end PhiNModule
