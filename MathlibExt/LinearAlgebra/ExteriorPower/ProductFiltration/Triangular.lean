/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration.FirstSummandMap
public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration.RelativeProjection

/-!
# Triangular maps preserve mixed exterior filtration

A first-summand-preserving linear map `f : M×N → M'×N'` over a commutative ring preserves
every first-weight stage `F_m^q` under its degree-`m` exterior map.

On a mixed `(i,j)` tensor, the first part is controlled by `Λ^i f.first` and the second part
by the full image of the second inclusion. Replacing that full image by the relative map
changes the result by a vector in `F_(i+j)^(i+1)`.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum

universe u v w v' w'

namespace exteriorPower.ProductFiltration.FirstSummandMap

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {M' : Type v'} [AddCommGroup M'] [Module R M']
  {N' : Type w'} [AddCommGroup N'] [Module R N']
  (f : FirstSummandMap (R := R) (M := M) (N := N) (M' := M') (N' := N'))

/-- Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. For `i,j : ℕ`, `x ∈ Λ^i_R M`, and `y ∈ Λ^j_R N`, the image of the `(i,j)`-injection
of `x⊗y` is `Λ^i(inl')(Λ^i f.first x) * Λ^j(f.map ∘ inr)(y)` in the exterior algebra of
`M'×N'`. -/
theorem map_mixed (i j : ℕ) (x : ⋀[R]^i M) (y : ⋀[R]^j N) :
    exteriorPower.map (i + j) f.map
        (injection R M N (i + j) ⟨(i, j), rfl⟩ (x ⊗ₜ[R] y)) =
      leftBaseMultiply R M' N' i j (exteriorPower.map i f.first x)
        (exteriorPower.map j (f.map.comp (LinearMap.inr R M N)) y) := by
  apply Subtype.ext
  rw [exteriorPower.coe_map, injection_tmul_val, map_mul]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, f.first_commutes]
  change ExteriorAlgebra.map ((LinearMap.inl R M' N').comp f.first) x *
      ExteriorAlgebra.map f.map (ExteriorAlgebra.map (LinearMap.inr R M N) y) =
    (exteriorPower.map i (LinearMap.inl R M' N')
      (exteriorPower.map i f.first x) : ExteriorAlgebra R (M' × N')) *
        (exteriorPower.map j (f.map.comp (LinearMap.inr R M N)) y :
          ExteriorAlgebra R (M' × N'))
  rw [exteriorPower.coe_map, exteriorPower.coe_map, exteriorPower.coe_map,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply]

/-- Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. For `m,q : ℕ` and `z ∈ F_m^q(M,N)`, `Λ^m f.map(z) ∈ F_m^q(M',N')`. The stage is
defined by vanishing of mixed coordinates whose first degree is below `q`. -/
theorem map_mem_filtration (m q : ℕ) (z : ⋀[R]^m (M × N))
    (hz : z ∈ filtration R M N m q) :
    exteriorPower.map m f.map z ∈ filtration R M' N' m q := by
  have h : ∀ y : exteriorPower.productPieces R M N m,
      exteriorPower.map m f.map
        ((exteriorPower.productEquiv R M N m).symm (clip R M N m q y)) ∈
          filtration R M' N' m q := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add y y' hy hy' => simpa only [map_add] using Submodule.add_mem _ hy hy'
    | of p t =>
      rw [← DirectSum.lof_eq_of R, clip_of]
      split_ifs with hp
      · change exteriorPower.map m f.map (injection R M N m p t) ∈ _
        rcases p with ⟨⟨i, j⟩, hij⟩
        subst m
        induction t using TensorProduct.inductionOn with
        | add t t' ht ht' => simpa only [map_add] using Submodule.add_mem _ ht ht'
        | tmul x y =>
          rw [map_mixed]
          apply filtration_antitone R M' N' (i + j) hp
          have hzero : exteriorPower.map j (f.map.comp (LinearMap.inr R M N)) y ∈
              filtration R M' N' j 0 := by rw [filtration_zero]; trivial
          simpa only [Nat.add_zero] using
            leftBaseMultiply_mem R M' N' i j 0 (exteriorPower.map i f.first x) _ hzero
      · simp only [map_zero]; exact Submodule.zero_mem _
  have h' := h (exteriorPower.productEquiv R M N m z)
  rw [clip_equiv_of_mem R M N m q z hz, LinearEquiv.symm_apply_apply] at h'
  exact h'

/-- Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. The maps satisfy `snd' ∘ f.map ∘ inr = f.relative : N →ₗ[R] N'`. -/
theorem relative_inr_square :
    (LinearMap.snd R M' N').comp (f.map.comp (LinearMap.inr R M N)) = f.relative := rfl

/-- Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. For `i,j : ℕ`, `x ∈ Λ^i_R M`, and `y ∈ Λ^j_R N`, the difference between
`Λ^(i+j)f.map(injection(x⊗y))` and the `(i,j)`-injection of `Λ^i f.first(x) ⊗ Λ^j
f.relative(y)` lies in `F_(i+j)^(i+1)(M',N')`. -/
theorem mixed_difference_mem_next (i j : ℕ) (x : ⋀[R]^i M) (y : ⋀[R]^j N) :
    exteriorPower.map (i + j) f.map
        (injection R M N (i + j) ⟨(i, j), rfl⟩ (x ⊗ₜ[R] y)) -
      injection R M' N' (i + j) ⟨(i, j), rfl⟩
        (exteriorPower.map i f.first x ⊗ₜ[R] exteriorPower.map j f.relative y) ∈
          filtration R M' N' (i + j) (i + 1) := by
  rw [map_mixed, ← leftBaseMultiply_map_inr]
  have hrelative : exteriorPower.map j (LinearMap.inr R M' N')
      (exteriorPower.map j f.relative y) =
        exteriorPower.map j ((LinearMap.inr R M' N').comp f.relative) y :=
    (LinearMap.congr_fun
      (exteriorPower.map_comp (n := j) f.relative (LinearMap.inr R M' N')) y).symm
  rw [hrelative, ← (leftBaseMultiply R M' N' i j (exteriorPower.map i f.first x)).map_sub]
  apply leftBaseMultiply_mem R M' N' i j 1
  exact map_difference_mem_first R M' N'
    (f.map.comp (LinearMap.inr R M N)) f.relative f.relative_inr_square j y

theorem mixed_difference_mem_next_of_index (m : ℕ) (p : Index m)
    (x : ⋀[R]^p.val.1 M) (y : ⋀[R]^p.val.2 N) :
    exteriorPower.map m f.map (injection R M N m p (x ⊗ₜ[R] y)) -
        injection R M' N' m p
          (exteriorPower.map p.val.1 f.first x ⊗ₜ[R] exteriorPower.map p.val.2 f.relative y) ∈
      filtration R M' N' m (p.val.1 + 1) := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  subst m
  exact f.mixed_difference_mem_next i j x y

end exteriorPower.ProductFiltration.FirstSummandMap

end
