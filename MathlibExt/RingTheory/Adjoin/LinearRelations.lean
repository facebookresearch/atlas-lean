/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions adapted from `P2M/Sol/` in anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
* S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra.lean
* S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot.lean
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib, copyright its respective authors,
released under the Apache License, Version 2.0. No individual authors are
identified for these two source files in the upstream ATTRIBUTION.md.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.Ring

/-!
# Algebra homomorphisms from linearly consistent generator assignments

An assignment on a multiplicatively closed family containing one extends to
its generated algebra if it preserves all finite linear relations.
-/

public section

namespace Algebra

private theorem exists_algHom_adjoin_of_ker_le
    {K F L ι : Type*} [Field K] [Ring F] [Ring L]
    [Algebra K F] [Algebra K L] (t : ι → F) (a : ι → L)
    (hone : ∃ i₀, t i₀ = 1 ∧ a i₀ = 1)
    (hmul : ∀ i j, ∃ k, t k = t i * t j ∧ a k = a i * a j)
    (hker : LinearMap.ker (Finsupp.linearCombination K t) ≤
      LinearMap.ker (Finsupp.linearCombination K a)) :
    ∃ χ : adjoin K (Set.range t) →ₐ[K] L,
      ∀ i, χ ⟨t i, subset_adjoin (Set.mem_range_self i)⟩ = a i := by
  classical
  obtain ⟨i₀, ht₀, ha₀⟩ := hone
  let S := adjoin K (Set.range t)
  let M : Submonoid F :=
    { carrier := Set.range t
      one_mem' := ⟨i₀, ht₀⟩
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        obtain ⟨k, hk, -⟩ := hmul i j
        exact ⟨k, hk⟩ }
  have hSspan : S.toSubmodule = Submodule.span K (Set.range t) := by
    rw [adjoin_eq_span]
    change Submodule.span K (Submonoid.closure (M : Set F) : Set F) = _
    rw [Submonoid.closure_eq]
    rfl
  let Lt := Finsupp.linearCombination K t
  let La := Finsupp.linearCombination K a
  have hrange : LinearMap.range Lt = S.toSubmodule := by
    rw [hSspan]
    exact Finsupp.range_linearCombination K
  let φ₀ := (LinearMap.ker Lt).liftQ La hker
  let e := Lt.quotKerEquivRange
  let φ : S →ₗ[K] L :=
    { toFun := fun s => φ₀ (e.symm ⟨s, hrange.symm ▸ s.property⟩)
      map_add' := fun x y => by rw [← map_add φ₀, ← map_add e.symm]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← map_smul φ₀, ← map_smul e.symm]; rfl }
  let v : ι → S := fun i => ⟨t i, subset_adjoin (Set.mem_range_self i)⟩
  have hφv : ∀ i, φ (v i) = a i := by
    intro i
    have ht : Lt (Finsupp.single i 1) = t i := by
      simp [Lt, Finsupp.linearCombination_single]
    change φ₀ (e.symm ⟨t i, _⟩) = a i
    have ht' : (⟨t i, hrange.symm ▸ (v i).property⟩ : LinearMap.range Lt) =
        ⟨Lt (Finsupp.single i 1), LinearMap.mem_range_self _ _⟩ := Subtype.ext ht.symm
    rw [ht', LinearMap.quotKerEquivRange_symm_apply_image]
    simp [φ₀, La, Finsupp.linearCombination_single]
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := S.val.toLinearMap)
      (fun x y h => Subtype.ext h)
    rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp]
    have hval : LinearMap.range S.val.toLinearMap = S.toSubmodule := by
      ext x
      exact ⟨fun ⟨s, hs⟩ => hs ▸ s.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hval, hSspan]
    rfl
  have hmul' : ∀ x y : S, φ (x * y) = φ x * φ y := by
    have hB : (LinearMap.mul K S).compr₂ φ =
        (LinearMap.mul K L).compl₁₂ φ φ := by
      refine LinearMap.ext_on_range hv fun i => LinearMap.ext_on_range hv fun j => ?_
      obtain ⟨k, hk, hak⟩ := hmul i j
      have hvk : v i * v j = v k := Subtype.ext hk.symm
      change φ (v i * v j) = φ (v i) * φ (v j)
      rw [hvk, hφv, hφv, hφv, hak]
    exact fun x y => congrArg (fun B : S →ₗ[K] S →ₗ[K] L => B x y) hB
  have hone' : φ 1 = 1 := by
    have h : (1 : S) = v i₀ := Subtype.ext ht₀.symm
    rw [h, hφv, ha₀]
  exact ⟨AlgHom.ofLinearMap φ hone' hmul', hφv⟩

/-- **Algebra maps from relation-preserving generator assignments.**
A unital, multiplicatively consistent assignment on generators extends to
an algebra homomorphism when it preserves every finite linear relation.

The index family need not be injective or finite; the target may have zero
divisors. This preserves the full statement of the source theorem
`exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra`. -/
theorem exists_algHom_adjoin_of_linearRelations
    {K : Type*} [Field K] {F : Type*} [CommRing F] [Algebra K F]
    (L : Type*) [CommRing L] [Algebra K L]
    {ι : Type*} (t : ι → F) (a : ι → L)
    (hone : ∃ i₀, t i₀ = 1 ∧ a i₀ = 1)
    (hmul : ∀ i j, ∃ k, t k = t i * t j ∧ a k = a i * a j)
    (hcons : ∀ (n : ℕ) (idx : Fin n → ι) (c : Fin n → K),
      ∑ l, c l • t (idx l) = 0 → ∑ l, c l • a (idx l) = 0) :
    ∃ χ : adjoin K (Set.range t) →ₐ[K] L,
      ∀ i, χ ⟨t i, subset_adjoin (Set.mem_range_self i)⟩ = a i := by
  classical
  apply exists_algHom_adjoin_of_ker_le t a hone hmul
  intro l hl
  change Finsupp.linearCombination K a l = 0
  change Finsupp.linearCombination K t l = 0 at hl
  simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hl ⊢
  let e := l.support.equivFin
  have ht : ∑ m : Fin l.support.card, l (e.symm m) • t (e.symm m) =
      ∑ i ∈ l.support, l i • t i := by
    rw [← Finset.sum_coe_sort l.support (fun i => l i • t i)]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  have ha : ∑ m : Fin l.support.card, l (e.symm m) • a (e.symm m) =
      ∑ i ∈ l.support, l i • a i := by
    rw [← Finset.sum_coe_sort l.support (fun i => l i • a i)]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  rw [← ha]
  exact hcons _ (fun m => e.symm m) (fun m => l (e.symm m)) (by rw [ht, hl])

private theorem exists_int_of_mem_primeSubfield {κ : Type*} [Field κ]
    {x : κ} (hx : x ∈ (⊥ : Subfield κ)) :
    ∃ m d : ℤ, (d : κ) ≠ 0 ∧ x * (d : κ) = (m : κ) := by
  rw [← Subfield.closure_empty, Subfield.mem_closure_iff] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := hx
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨d, rfl⟩ := hz
  by_cases hd : (d : κ) = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← hyz, hd, div_zero]
    simp
  · exact ⟨m, d, hd, by rw [← hyz, div_mul_cancel₀ _ hd]⟩

private theorem sum_mul_eq_zero_of_primeSubfield
    {κ B T : Type*} [Field κ] [Ring B] [Algebra κ B] [CommRing T]
    (red : T →+* B) (ρ : T →+* κ)
    (hker : ∀ t, red t = 0 → ρ t = 0)
    (s : Finset T) (a : T → κ) (ha : ∀ t, a t ∈ (⊥ : Subfield κ))
    (hrel : ∑ t ∈ s, a t • red t = 0) : ∑ t ∈ s, a t * ρ t = 0 := by
  classical
  choose m d hd hmd using fun t => exists_int_of_mem_primeSubfield (ha t)
  let D : κ := ∏ t ∈ s, (d t : κ)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hd t
  let Z : T → ℤ := fun t => m t * ∏ t' ∈ s.erase t, d t'
  have hZ : ∀ t ∈ s, (Z t : κ) = D * a t := by
    intro t ht
    simp only [Z, Int.cast_mul, Int.cast_prod]
    rw [← hmd t]
    dsimp [D]
    rw [← Finset.mul_prod_erase s (fun t => (d t : κ)) ht]
    ring
  have hred : red (∑ t ∈ s, (Z t : T) * t) = 0 := by
    rw [map_sum]
    calc
      ∑ t ∈ s, red ((Z t : T) * t) = ∑ t ∈ s, D • (a t • red t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [map_mul, map_intCast, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul κ,
          hZ t ht, mul_smul]
      _ = 0 := by rw [← Finset.smul_sum, hrel, smul_zero]
  have hρ := hker _ hred
  rw [map_sum] at hρ
  have hsum : D * (∑ t ∈ s, a t * ρ t) = 0 := by
    rw [Finset.mul_sum]
    convert hρ using 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_mul, map_intCast, hZ t ht, mul_assoc]
  exact (mul_eq_zero.mp hsum).resolve_left hD

/-- **Extending a ring character via prime-subfield-valued linear forms.**
A ring character extends to the algebra generated by another ring image
when its kernel contains the first kernel and a separating family of linear
forms takes prime-subfield values on that image.

The ambient algebra may be noncommutative, and the separating family may be
infinite. The prime subfield is `⊥ : Subfield κ`, in any characteristic.
This is the source theorem
`exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot`. -/
theorem exists_algHom_adjoin_of_primeSubfield
    {κ : Type*} [Field κ] {B : Type*} [Ring B] [Algebra κ B]
    {ι : Type*} (c : ι → (B →ₗ[κ] κ)) (hc : ∀ b : B, (∀ i, c i b = 0) → b = 0)
    {T : Type*} [CommRing T] (red : T →+* B) (ρ : T →+* κ)
    (hbot : ∀ (t : T) (i : ι), c i (red t) ∈ (⊥ : Subfield κ))
    (hker : ∀ t : T, red t = 0 → ρ t = 0) :
    ∃ χ : adjoin κ (Set.range red) →ₐ[κ] κ,
      ∀ t : T, χ ⟨red t, subset_adjoin (Set.mem_range_self t)⟩ = ρ t := by
  classical
  apply exists_algHom_adjoin_of_ker_le red ρ
    ⟨1, map_one red, map_one ρ⟩
    (fun i j => ⟨i * j, map_mul red i j, map_mul ρ i j⟩)
  intro l hl
  change Finsupp.linearCombination κ ρ l = 0
  change Finsupp.linearCombination κ red l = 0 at hl
  simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hl ⊢
  let P : Subfield κ := ⊥
  let b := Module.Free.chooseBasis P κ
  let s := l.support.biUnion fun t => (b.repr (l t)).support
  have hcoeff (j : Module.Free.ChooseBasisIndex P κ) :
      ∑ t ∈ l.support, ((b.repr (l t) j : P) : κ) * ρ t = 0 := by
    apply sum_mul_eq_zero_of_primeSubfield red ρ hker l.support
      (fun t => (b.repr (l t) j : κ)) (fun t => (b.repr (l t) j).property)
    apply hc
    intro i
    have h : ∑ t ∈ l.support, (⟨c i (red t), hbot t i⟩ : P) • l t = 0 := by
      change ∑ t ∈ l.support, c i (red t) * l t = 0
      simpa [map_sum, map_smul, smul_eq_mul, mul_comm] using congrArg (c i) hl
    have hh := congrArg (fun x => (b.repr x) j) h
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.zero_apply] at hh
    have hh' := congrArg (fun x : P => (x : κ)) hh
    simpa [map_sum, map_smul, smul_eq_mul, mul_comm] using hh'
  have hexpand (t : T) (ht : t ∈ l.support) :
      ∑ j ∈ s, (b.repr (l t) j : P) • b j = l t := by
    calc
      _ = ∑ j ∈ (b.repr (l t)).support, (b.repr (l t) j : P) • b j := by
        symm
        apply Finset.sum_subset
        · exact Finset.subset_biUnion_of_mem (fun t => (b.repr (l t)).support) ht
        · intro j _ hj
          rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
      _ = l t := b.linearCombination_repr (l t)
  calc
    ∑ t ∈ l.support, l t • ρ t =
        ∑ t ∈ l.support, (∑ j ∈ s, (b.repr (l t) j : P) • b j) * ρ t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hexpand t ht, smul_eq_mul]
    _ = ∑ j ∈ s, b j * (∑ t ∈ l.support, (b.repr (l t) j : κ) * ρ t) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro t _
      change (b.repr (l t) j : κ) * b j * ρ t = _
      ring
    _ = 0 := by simp only [hcoeff, mul_zero, Finset.sum_const_zero]

end Algebra
