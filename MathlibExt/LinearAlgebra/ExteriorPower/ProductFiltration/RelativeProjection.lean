/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration.BaseMultiplication

/-!
# The relative exterior projection and first positive weight

The second projection `M×N → N` on degree `m` is the zero-first-weight coordinate of the
product decomposition, identified with `Λ^m_R N` by the degree-zero scalar unitor. Its kernel
is `F_m^1`.

If `h : V → M×N` has second component `b : V → N`, the difference `Λ^m h(y) - Λ^m(inr ∘ b)(y)`
lies in `F_m^1`. In degree zero the exterior projection is the identity scalar map.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum

universe u v w z

namespace exteriorPower.ProductFiltration

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/-- For a commutative ring `R`, `R`-modules `M,V`, and `n : ℕ`, `exteriorPower.map (n+1) (0 : M
→ₗ[R] V)=0`. -/
theorem map_succ_zero {V : Type z} [AddCommGroup V] [Module R V] (n : ℕ) :
    exteriorPower.map (n + 1) (0 : M →ₗ[R] V) = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change exteriorPower.map (n + 1) (0 : M →ₗ[R] V) (exteriorPower.ιMulti R (n + 1) a) = 0
  rw [exteriorPower.map_apply_ιMulti]
  change (exteriorPower.ιMulti R (n + 1) (M := V)) (0 : Fin (n + 1) → V) = 0
  exact (exteriorPower.ιMulti R (n + 1) (M := V)).map_zero

theorem map_zero_of_ne_zero {V : Type z} [AddCommGroup V] [Module R V]
    (n : ℕ) (hn : n ≠ 0) : exteriorPower.map n (0 : M →ₗ[R] V) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact map_succ_zero R M k

/-- For a commutative ring `R`, an `R`-module `M`, and `x ∈ Λ^0_R M`, the underlying exterior
element is `algebraMap R (ExteriorAlgebra R M) (exteriorPower.zeroEquiv R M x)`. -/
theorem zeroPower_value (x : ⋀[R]^0 M) :
    (x : ExteriorAlgebra R M) = algebraMap R (ExteriorAlgebra R M) (exteriorPower.zeroEquiv R M x) := by
  have hx : x = (exteriorPower.zeroEquiv R M x) • exteriorPower.ιMulti R 0 (fun i => Fin.elim0 i) := by
    apply (exteriorPower.zeroEquiv R M).injective
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  conv_lhs => rw [hx]
  change (exteriorPower.zeroEquiv R M x) •
      ExteriorAlgebra.ιMulti R 0 (fun i => Fin.elim0 i) = _
  rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. Write `P_m=⊕_(a+b=m) Λ^a_R M ⊗[R]
Λ^b_R N`, `E_m : Λ^m_R(M×N) ≃ P_m`, and `F_m^q` for the descending stage whose coordinates
with first degree `a<q` vanish. For `m : ℕ`, the `R`-linear equivalence `Λ^0_R M ⊗[R] Λ^m_R N
≃ₗ[R] Λ^m_R N` sends `x⊗y` to `zeroEquiv R M x • y`. -/
def zeroCoordinateEquiv (m : ℕ) :
    Piece R M N m (index m 0 (Nat.zero_le m)) ≃ₗ[R] (⋀[R]^m N) :=
  (TensorProduct.congr (exteriorPower.zeroEquiv R M) (LinearEquiv.refl R (⋀[R]^m N))).trans
    (TensorProduct.lid R (⋀[R]^m N))

theorem zeroCoordinateEquiv_tmul (m : ℕ) (x : ⋀[R]^0 M) (y : ⋀[R]^m N) :
    zeroCoordinateEquiv R M N m (x ⊗ₜ[R] y) = exteriorPower.zeroEquiv R M x • y := rfl

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. Write `P_m=⊕_(a+b=m) Λ^a_R M ⊗[R]
Λ^b_R N`, `E_m : Λ^m_R(M×N) ≃ P_m`, and `F_m^q` for the descending stage whose coordinates
with first degree `a<q` vanish. For `a+b=m`, `x ∈ Λ^a_R M`, and `y ∈ Λ^b_R N`, the underlying
value of `Λ^m(snd)(injection(x⊗y))` is `ExteriorAlgebra.map (0 : M →ₗ[R] N)(x) * y`. -/
theorem map_snd_injection_val (m : ℕ) (p : Index m)
    (x : ⋀[R]^p.val.1 M) (y : ⋀[R]^p.val.2 N) :
    (exteriorPower.map m (LinearMap.snd R M N) (injection R M N m p (x ⊗ₜ[R] y)) :
      ExteriorAlgebra R N) =
        ExteriorAlgebra.map (0 : M →ₗ[R] N) x * y.val := by
  rw [exteriorPower.coe_map, injection_tmul_val, map_mul]
  have hleft : (LinearMap.snd R M N).comp (LinearMap.inl R M N) = 0 := by ext x <;> rfl
  have hright : (LinearMap.snd R M N).comp (LinearMap.inr R M N) = LinearMap.id := by ext x <;> rfl
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hleft,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hright,
    ExteriorAlgebra.map_id, AlgHom.id_apply]

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. Write `P_m=⊕_(a+b=m) Λ^a_R M ⊗[R]
Λ^b_R N`, `E_m : Λ^m_R(M×N) ≃ P_m`, and `F_m^q` for the descending stage whose coordinates
with first degree `a<q` vanish. For `z ∈ Λ^m_R(M×N)`, `Λ^m(snd)(z)=zeroCoordinateEquiv R M N m
(coordinate_(0,m)(z))`. -/
theorem map_snd_coordinate (m : ℕ) (z : ⋀[R]^m (M × N)) :
    exteriorPower.map m (LinearMap.snd R M N) z =
      zeroCoordinateEquiv R M N m (coordinate R M N m (index m 0 (Nat.zero_le m)) z) := by
  have h : ∀ y : exteriorPower.productPieces R M N m,
      exteriorPower.map m (LinearMap.snd R M N) ((exteriorPower.productEquiv R M N m).symm y) =
        zeroCoordinateEquiv R M N m
          (coordinate R M N m (index m 0 (Nat.zero_le m))
            ((exteriorPower.productEquiv R M N m).symm y)) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simpa only [map_add] using congrArg₂ (· + ·) hy hy'
    | of p t =>
      change exteriorPower.map m (LinearMap.snd R M N) (injection R M N m p t) =
        zeroCoordinateEquiv R M N m
          (coordinate R M N m (index m 0 (Nat.zero_le m)) (injection R M N m p t))
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
      | tmul x y =>
        by_cases hp : p.val.1 = 0
        · have heq : p = index m 0 (Nat.zero_le m) := by
            apply Subtype.ext
            apply Prod.ext <;> have hsum := p.property <;> dsimp [index] <;> omega
          subst p
          rw [coordinate_injection_same]
          have hzero : zeroCoordinateEquiv R M N m (x ⊗ₜ[R] y) =
              exteriorPower.zeroEquiv R M x • y := zeroCoordinateEquiv_tmul R M N m x y
          refine Eq.trans ?_ hzero.symm
          apply Subtype.ext
          rw [map_snd_injection_val]
          let x0 : ⋀[R]^0 M := x
          let y0 : ⋀[R]^m N := y
          change ExteriorAlgebra.map (0 : M →ₗ[R] N) x0.val * y0.val =
            (exteriorPower.zeroEquiv R M x0) • y0.val
          have hx0 := zeroPower_value R M x0
          have hmap : ExteriorAlgebra.map (0 : M →ₗ[R] N) x0.val =
              algebraMap R (ExteriorAlgebra R N) (exteriorPower.zeroEquiv R M x0) :=
            (congrArg (ExteriorAlgebra.map (0 : M →ₗ[R] N)) hx0).trans
              ((ExteriorAlgebra.map (0 : M →ₗ[R] N)).commutes (exteriorPower.zeroEquiv R M x0))
          exact (congrArg (fun t : ExteriorAlgebra R N => t * y0.val) hmap).trans
            (Algebra.smul_def (exteriorPower.zeroEquiv R M x0) y0.val).symm
        · have hne : index m 0 (Nat.zero_le m) ≠ p := by
            intro h
            exact hp (congrArg (fun p : Index m => p.val.1) h.symm)
          rw [coordinate_injection_ne R M N m _ p hne, map_zero]
          apply Subtype.ext
          rw [map_snd_injection_val]
          have hx : ExteriorAlgebra.map (0 : M →ₗ[R] N) x = 0 := by
            have hpow := LinearMap.congr_fun
              (map_zero_of_ne_zero R M (V := N) p.val.1 hp) x
            have hzero : exteriorPower.map p.val.1 (0 : M →ₗ[R] N) x = (0 : ⋀[R]^p.val.1 N) :=
              hpow.trans (LinearMap.zero_apply x)
            exact (exteriorPower.coe_map (n := p.val.1) (0 : M →ₗ[R] N) x).symm.trans
              ((congrArg (fun t : ⋀[R]^p.val.1 N => t.val) hzero).trans Submodule.coe_zero)
          exact (congrArg (fun t : ExteriorAlgebra R N => t * y.val) hx).trans (zero_mul y.val)
  simpa only [LinearEquiv.symm_apply_apply] using h (exteriorPower.productEquiv R M N m z)

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. Write `P_m=⊕_(a+b=m) Λ^a_R M ⊗[R]
Λ^b_R N`, `E_m : Λ^m_R(M×N) ≃ P_m`, and `F_m^q` for the descending stage whose coordinates
with first degree `a<q` vanish. For every `m : ℕ`, `ker(Λ^m(snd)) = F_m^1`. -/
theorem ker_map_snd (m : ℕ) :
    (exteriorPower.map m (LinearMap.snd R M N)).ker = filtration R M N m 1 := by
  ext z
  change exteriorPower.map m (LinearMap.snd R M N) z = 0 ↔
    ∀ p : Index m, p.val.1 < 1 → coordinate R M N m p z = 0
  rw [map_snd_coordinate, (zeroCoordinateEquiv R M N m).map_eq_zero_iff]
  constructor
  · intro hz p hp
    have heq : p = index m 0 (Nat.zero_le m) := by
      apply Subtype.ext
      apply Prod.ext <;> have hsum := p.property <;> dsimp [index] <;> omega
    subst p
    exact hz
  · intro hz
    exact hz (index m 0 (Nat.zero_le m)) (by dsimp [index]; omega)

/-- Let `R` be a commutative ring and `M,N` be `R`-modules. Write `P_m=⊕_(a+b=m) Λ^a_R M ⊗[R]
Λ^b_R N`, `E_m : Λ^m_R(M×N) ≃ P_m`, and `F_m^q` for the descending stage whose coordinates
with first degree `a<q` vanish. Let `V` be an `R`-module, `h : V →ₗ[R] M×N`, and `b : V →ₗ[R]
N` satisfy `snd ∘ h=b`. For `m : ℕ` and `y ∈ Λ^m_R V`, `Λ^m h(y)-Λ^m(inr ∘ b)(y) ∈ F_m^1`. -/
theorem map_difference_mem_first
    {V : Type z} [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] M × N) (b : V →ₗ[R] N)
    (hb : (LinearMap.snd R M N).comp h = b)
    (m : ℕ) (y : ⋀[R]^m V) :
    exteriorPower.map m h y -
        exteriorPower.map m ((LinearMap.inr R M N).comp b) y ∈ filtration R M N m 1 := by
  rw [← ker_map_snd]
  change exteriorPower.map m (LinearMap.snd R M N)
    (exteriorPower.map m h y - exteriorPower.map m ((LinearMap.inr R M N).comp b) y) = 0
  have hb' : (LinearMap.snd R M N).comp ((LinearMap.inr R M N).comp b) = b := by ext x <;> rfl
  rw [map_sub, ← LinearMap.comp_apply, ← exteriorPower.map_comp, hb,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp, hb', sub_self]

end exteriorPower.ProductFiltration

end
