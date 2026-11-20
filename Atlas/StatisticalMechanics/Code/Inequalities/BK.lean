/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Code.Inequalities.DisjointOccurrence
import Code.Foundations.ProductMeasure
import Code.Inequalities.IncreasingEvent

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace



variable {E F : Type*}


def pweight [Fintype E] (φ : E → Bool → ℝ) (ω : ConfigSpace E) : ℝ := ∏ x, φ x (ω x)


lemma pweight_nonneg [Fintype E] {φ : E → Bool → ℝ} (hφ : ∀ x b, 0 ≤ φ x b)
    (ω : ConfigSpace E) : 0 ≤ pweight φ ω :=
  Finset.prod_nonneg (fun x _ => hφ x (ω x))


noncomputable def wprob [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (S : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω


lemma wprob_mono [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ} (hφ : ∀ x b, 0 ≤ φ x b)
    {S T : Set (ConfigSpace E)} (h : S ⊆ T) : wprob φ S ≤ wprob φ T := by
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right _ (pweight_nonneg hφ ω)
  by_cases hS : ω ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (h hS)]
  · rw [Set.indicator_of_notMem hS]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω



lemma wprob_union_inter [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (U V : Set (ConfigSpace E)) :
    wprob φ (U ∪ V) + wprob φ (U ∩ V) = wprob φ U + wprob φ V := by
  simp only [wprob, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hU : ω ∈ U <;> by_cases hV : ω ∈ V <;>
    simp [Set.indicator, hU, hV, Set.mem_union, Set.mem_inter_iff]







lemma bk_algebra (a0 a1 b0 b1 p q c0 c1 m : ℝ)
    (hq : q = 1 - p) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hmab : m ≤ a0 * b0) (hc0m : c0 ≤ m)
    (hc1u : c1 ≤ a0 * b1 + a1 * b0 - m) (hc1v : c1 ≤ a1 * b1) :
    q * c0 + p * c1 ≤ (q * a0 + p * a1) * (q * b0 + p * b1) := by
  have key1 : q * p * c1 ≤ q * p * (a0 * b1 + a1 * b0 - m) :=
    mul_le_mul_of_nonneg_left hc1u (mul_nonneg hq0 hp0)
  have key2 : p * p * c1 ≤ p * p * (a1 * b1) :=
    mul_le_mul_of_nonneg_left hc1v (mul_nonneg hp0 hp0)
  have key3 : q * c0 ≤ q * m := mul_le_mul_of_nonneg_left hc0m hq0
  have key4 : q * q * m ≤ q * q * (a0 * b0) :=
    mul_le_mul_of_nonneg_left hmab (mul_nonneg hq0 hq0)
  have hpsplit : p * c1 = q * p * c1 + p * p * c1 := by rw [hq]; ring
  have hqsq : q * m = q * q * m + q * p * m := by rw [hq]; ring
  calc q * c0 + p * c1
      ≤ q * m + (q * p * c1 + p * p * c1) := by rw [hpsplit]; linarith [key3]
    _ ≤ q * m + (q * p * (a0 * b1 + a1 * b0 - m) + p * p * (a1 * b1)) := by linarith [key1, key2]
    _ = (q * q * m + q * p * m) + (q * p * (a0 * b1 + a1 * b0 - m) + p * p * (a1 * b1)) := by
          rw [hqsq]
    _ ≤ (q * q * (a0 * b0) + q * p * m)
          + (q * p * (a0 * b1 + a1 * b0 - m) + p * p * (a1 * b1)) := by linarith [key4]
    _ = (q * a0 + p * a1) * (q * b0 + p * b1) := by ring





def slice {n : ℕ} (C : Set (ConfigSpace (Fin (n + 1)))) (x : Bool) :
    Set (ConfigSpace (Fin n)) := {ω' | Fin.cons x ω' ∈ C}


def sliceSet {n : ℕ} (K : Set (Fin (n + 1))) : Set (Fin n) := {j | j.succ ∈ K}

lemma indicator_slice {n : ℕ} (S : Set (ConfigSpace (Fin (n + 1)))) (x : Bool)
    (ω' : ConfigSpace (Fin n)) :
    S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω')
      = (slice S x).indicator (fun _ => (1 : ℝ)) ω' := rfl



lemma pweight_cons {n : ℕ} (φ : Fin (n + 1) → Bool → ℝ) (x : Bool) (ω' : ConfigSpace (Fin n)) :
    pweight φ (Fin.cons x ω') = φ 0 x * pweight (fun j => φ j.succ) ω' := by
  simp only [pweight]
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  exact congrArg _ (Finset.prod_congr rfl (fun j _ => by rw [Fin.cons_succ]))



theorem wprob_slice {n : ℕ} (φ : Fin (n + 1) → Bool → ℝ) (S : Set (ConfigSpace (Fin (n + 1)))) :
    wprob φ S = φ 0 false * wprob (fun j => φ j.succ) (slice S false)
             + φ 0 true * wprob (fun j => φ j.succ) (slice S true) := by
  have hx : ∀ x : Bool, ∑ ω' : ConfigSpace (Fin n),
      S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω') * pweight φ (Fin.cons x ω')
      = φ 0 x * wprob (fun j => φ j.succ) (slice S x) := by
    intro x
    simp only [wprob, indicator_slice, pweight_cons, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω' _; ring
  calc wprob φ S = ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω := rfl
    _ = ∑ p : Bool × ConfigSpace (Fin n),
          S.indicator (fun _ => (1 : ℝ)) (Fin.cons p.1 p.2) * pweight φ (Fin.cons p.1 p.2) :=
          (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ (fun p => rfl)).symm
    _ = ∑ x : Bool, ∑ ω' : ConfigSpace (Fin n),
          S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω') * pweight φ (Fin.cons x ω') :=
          Fintype.sum_prod_type _
    _ = φ 0 false * wprob (fun j => φ j.succ) (slice S false)
             + φ 0 true * wprob (fun j => φ j.succ) (slice S true) := by
          rw [Fintype.sum_bool, hx false, hx true]; ring




lemma slice_isIncreasing {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))} (hC : IsIncreasing C)
    (x : Bool) : IsIncreasing (slice C x) := by
  intro a b hab ha
  simp only [slice, Set.mem_setOf_eq] at ha ⊢
  apply hC _ ha
  intro i; refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero]
  · intro j; simp only [Fin.cons_succ]; exact hab j


lemma slice_false_subset_true {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    (hC : IsIncreasing C) : slice C false ⊆ slice C true := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq] at hω' ⊢
  apply hC _ hω'
  intro i; refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero]
  · intro j; simp [Fin.cons_succ]



lemma occursOn_slice_of_false {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {ω' : ConfigSpace (Fin n)}
    (h : OccursOn C K (Fin.cons false ω')) :
    OccursOn (slice C false) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_setOf_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro _; simp [Fin.cons_zero]
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj



lemma occursOn_slice_true {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {ω' : ConfigSpace (Fin n)}
    (h : OccursOn C K (Fin.cons true ω')) :
    OccursOn (slice C true) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_setOf_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro _; simp [Fin.cons_zero]
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj



lemma occursOn_slice_false_notmem {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {x : Bool} {ω' : ConfigSpace (Fin n)}
    (h0 : (0 : Fin (n + 1)) ∉ K) (h : OccursOn C K (Fin.cons x ω')) :
    OccursOn (slice C false) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_setOf_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro hi0; exact absurd hi0 h0
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj


lemma sliceSet_disjoint {n : ℕ} {K L : Set (Fin (n + 1))} (h : Disjoint K L) :
    Disjoint (sliceSet K) (sliceSet L) := by
  rw [Set.disjoint_left] at h ⊢
  intro j hjK hjL
  exact h (a := j.succ) hjK hjL



theorem slice_disjointOccurrence_false {n : ℕ} {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) false ⊆
      disjointOccurrence (slice A false) (slice B false) := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
    occursOn_slice_of_false hA, occursOn_slice_of_false hB⟩



theorem slice_disjointOccurrence_true {n : ℕ} {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) true ⊆
      disjointOccurrence (slice A false) (slice B true) ∪
      disjointOccurrence (slice A true) (slice B false) := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  by_cases h0K : (0 : Fin (n + 1)) ∈ K
  · have h0L : (0 : Fin (n + 1)) ∉ L := by rw [Set.disjoint_left] at hKL; exact hKL h0K
    right
    exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
      occursOn_slice_true hA, occursOn_slice_false_notmem h0L hB⟩
  · left
    exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
      occursOn_slice_false_notmem h0K hA, occursOn_slice_true hB⟩






lemma occursOn_subsingleton {n : ℕ} [Subsingleton (ConfigSpace (Fin n))]
    {A : Set (ConfigSpace (Fin n))} {K : Set (Fin n)} {ω : ConfigSpace (Fin n)} :
    OccursOn A K ω ↔ ω ∈ A := by
  refine ⟨OccursOn.mem_self, fun h ω' _ => ?_⟩
  rwa [Subsingleton.elim ω' ω]

lemma disjointOccurrence_subsingleton {n : ℕ} [Subsingleton (ConfigSpace (Fin n))]
    (A B : Set (ConfigSpace (Fin n))) :
    disjointOccurrence A B = A ∩ B := by
  ext ω
  rw [mem_disjointOccurrence]
  refine ⟨fun ⟨_, _, _, hA, hB⟩ => ⟨occursOn_subsingleton.mp hA, occursOn_subsingleton.mp hB⟩,
    fun ⟨hA, hB⟩ => ⟨∅, ∅, by simp, occursOn_subsingleton.mpr hA, occursOn_subsingleton.mpr hB⟩⟩





theorem bk_wprob : ∀ (n : ℕ) (φ : Fin n → Bool → ℝ),
    (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
    ∀ (A B : Set (ConfigSpace (Fin n))), IsIncreasing A → IsIncreasing B →
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  intro n
  induction n with
  | zero =>
    intro φ hφ0 _ A B _ _
    have hpw : pweight φ (default : ConfigSpace (Fin 0)) = 1 := by
      simp [pweight]
    have hval : ∀ S : Set (ConfigSpace (Fin 0)),
        wprob φ S = S.indicator (fun _ => (1 : ℝ)) (default : ConfigSpace (Fin 0)) := by
      intro S
      simp only [wprob]
      rw [Fintype.sum_subsingleton _ (default : ConfigSpace (Fin 0)), hpw, mul_one]
    rw [hval, hval, hval, disjointOccurrence_subsingleton]
    have hAB : (A ∩ B).indicator (fun _ => (1 : ℝ))
        = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
        simp [Set.indicator, ha, hb, Set.mem_inter_iff]
    rw [hAB]
  | succ n ih =>
    intro φ hφ0 hφ1 A B hA hB
    set ψ : Fin n → Bool → ℝ := fun j => φ j.succ with hψ
    have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 i.succ b
    have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 i.succ
    set q := φ 0 false with hqdef
    set p := φ 0 true with hpdef
    have hq0 : 0 ≤ q := hφ0 0 false
    have hp0 : 0 ≤ p := hφ0 0 true
    have hqp : q + p = 1 := hφ1 0
    have hqeq : q = 1 - p := by linarith
    set A0 := slice A false
    set A1 := slice A true
    set B0 := slice B false
    set B1 := slice B true
    have hA0 : IsIncreasing A0 := slice_isIncreasing hA false
    have hA1 : IsIncreasing A1 := slice_isIncreasing hA true
    have hB0 : IsIncreasing B0 := slice_isIncreasing hB false
    have hB1 : IsIncreasing B1 := slice_isIncreasing hB true
    have hA01 : A0 ⊆ A1 := slice_false_subset_true hA
    have hB01 : B0 ⊆ B1 := slice_false_subset_true hB
    set a0 := wprob ψ A0
    set a1 := wprob ψ A1
    set b0 := wprob ψ B0
    set b1 := wprob ψ B1
    have indA0B0 : wprob ψ (disjointOccurrence A0 B0) ≤ a0 * b0 := ih ψ hψ0 hψ1 A0 B0 hA0 hB0
    have indU : wprob ψ (disjointOccurrence A0 B1) ≤ a0 * b1 := ih ψ hψ0 hψ1 A0 B1 hA0 hB1
    have indV : wprob ψ (disjointOccurrence A1 B0) ≤ a1 * b0 := ih ψ hψ0 hψ1 A1 B0 hA1 hB0
    have indA1B1 : wprob ψ (disjointOccurrence A1 B1) ≤ a1 * b1 := ih ψ hψ0 hψ1 A1 B1 hA1 hB1
    set U := disjointOccurrence A0 B1 with hU
    set V := disjointOccurrence A1 B0 with hV
    set m := wprob ψ (disjointOccurrence A0 B0) with hm
    have hsubUcapV : disjointOccurrence A0 B0 ⊆ U ∩ V :=
      Set.subset_inter (disjointOccurrence_mono (le_refl _) hB01)
        (disjointOccurrence_mono hA01 (le_refl _))
    have hUVsub : U ∪ V ⊆ disjointOccurrence A1 B1 :=
      Set.union_subset (disjointOccurrence_mono hA01 (le_refl _))
        (disjointOccurrence_mono (le_refl _) hB01)
    set c0 := wprob ψ (slice (disjointOccurrence A B) false) with hc0
    set c1 := wprob ψ (slice (disjointOccurrence A B) true) with hc1
    have hc0m : c0 ≤ m := wprob_mono hψ0 slice_disjointOccurrence_false
    have hc1UV : c1 ≤ wprob ψ (U ∪ V) := wprob_mono hψ0 slice_disjointOccurrence_true
    have hincl : wprob ψ (U ∪ V) = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := by
      have := wprob_union_inter ψ U V; linarith
    have hmUV : m ≤ wprob ψ (U ∩ V) := wprob_mono hψ0 hsubUcapV
    have hc1u : c1 ≤ a0 * b1 + a1 * b0 - m := by
      calc c1 ≤ wprob ψ (U ∪ V) := hc1UV
        _ = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := hincl
        _ ≤ a0 * b1 + a1 * b0 - m := by linarith [indU, indV, hmUV]
    have hc1v : c1 ≤ a1 * b1 :=
      calc c1 ≤ wprob ψ (U ∪ V) := hc1UV
        _ ≤ wprob ψ (disjointOccurrence A1 B1) := wprob_mono hψ0 hUVsub
        _ ≤ a1 * b1 := indA1B1
    have hmab : m ≤ a0 * b0 := indA0B0
    have hdec : wprob φ (disjointOccurrence A B) = q * c0 + p * c1 := by rw [wprob_slice]
    have hAdec : wprob φ A = q * a0 + p * a1 := by rw [wprob_slice]
    have hBdec : wprob φ B = q * b0 + p * b1 := by rw [wprob_slice]
    rw [hdec, hAdec, hBdec]
    exact bk_algebra a0 a1 b0 b1 p q c0 c1 m hqeq hp0 hq0 hmab hc0m hc1u hc1v





def cfgEquiv (e : E ≃ F) : ConfigSpace F ≃ ConfigSpace E where
  toFun ω := fun x => ω (e x)
  invFun ω := fun y => ω (e.symm y)
  left_inv ω := by funext y; simp
  right_inv ω := by funext x; simp

@[simp] lemma cfgEquiv_apply (e : E ≃ F) (ω : ConfigSpace F) (x : E) :
    cfgEquiv e ω x = ω (e x) := rfl

lemma cfgEquiv_mono (e : E ≃ F) {ω ω' : ConfigSpace F} (h : ω ≤ ω') :
    cfgEquiv e ω ≤ cfgEquiv e ω' := fun x => h (e x)


lemma isIncreasing_preimage (e : E ≃ F) {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    IsIncreasing ((cfgEquiv e) ⁻¹' A) := by
  intro ω ω' hωω' hω
  simp only [Set.mem_preimage] at hω ⊢
  exact hA (cfgEquiv_mono e hωω') hω

lemma agreeOn_cfgEquiv (e : E ≃ F) (K : Set E) (ωf ωf' : ConfigSpace F) :
    agreeOn (e '' K) ωf ωf' ↔ agreeOn K (cfgEquiv e ωf) (cfgEquiv e ωf') := by
  constructor
  · intro h x hx; simp only [cfgEquiv_apply]; exact h (e x) ⟨x, hx, rfl⟩
  · intro h y hy; obtain ⟨x, hx, rfl⟩ := hy; have := h x hx; simpa using this

lemma occursOn_cfgEquiv (e : E ≃ F) (A : Set (ConfigSpace E)) (K : Set E) (ωf : ConfigSpace F) :
    OccursOn ((cfgEquiv e) ⁻¹' A) (e '' K) ωf ↔ OccursOn A K (cfgEquiv e ωf) := by
  constructor
  · intro h ωe hωe
    have hsurj : ωe = cfgEquiv e ((cfgEquiv e).symm ωe) := ((cfgEquiv e).apply_symm_apply ωe).symm
    rw [hsurj]
    refine h _ ?_
    rw [agreeOn_cfgEquiv, (cfgEquiv e).apply_symm_apply ωe]; exact hωe
  · intro h ωf' hωf'; rw [agreeOn_cfgEquiv] at hωf'; exact h _ hωf'


theorem preimage_disjointOccurrence (e : E ≃ F) (A B : Set (ConfigSpace E)) :
    (cfgEquiv e) ⁻¹' (disjointOccurrence A B)
      = disjointOccurrence ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) := by
  ext ωf
  simp only [Set.mem_preimage, mem_disjointOccurrence]
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨e '' K, e '' L, (Set.disjoint_image_iff e.injective).mpr hKL,
      (occursOn_cfgEquiv e A K ωf).mpr hA, (occursOn_cfgEquiv e B L ωf).mpr hB⟩
  · rintro ⟨K', L', hKL', hA, hB⟩
    refine ⟨e.symm '' K', e.symm '' L', (Set.disjoint_image_iff e.symm.injective).mpr hKL', ?_, ?_⟩
    · have h := (occursOn_cfgEquiv e A (e.symm '' K') ωf).mp
      rw [Set.image_image] at h; simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hA
    · have h := (occursOn_cfgEquiv e B (e.symm '' L') ωf).mp
      rw [Set.image_image] at h; simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hB

lemma pweight_transfer [Fintype E] [Fintype F] (e : E ≃ F) (φ : E → Bool → ℝ)
    (ωf : ConfigSpace F) :
    pweight φ (cfgEquiv e ωf) = pweight (fun y => φ (e.symm y)) ωf := by
  simp only [pweight, cfgEquiv_apply]
  exact Fintype.prod_equiv e (fun x => φ x (ωf (e x))) (fun y => φ (e.symm y) (ωf y))
    (fun x => by simp)



lemma wprob_transfer [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E ≃ F) (φ : E → Bool → ℝ) (S : Set (ConfigSpace E)) :
    wprob φ S = wprob (fun y => φ (e.symm y)) ((cfgEquiv e) ⁻¹' S) := by
  simp only [wprob]
  rw [← Equiv.sum_comp (cfgEquiv e) (fun ω => S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω)]
  apply Finset.sum_congr rfl
  intro ωf _
  rw [pweight_transfer]
  congr 1




theorem bk_wprob_general [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  set n := Fintype.card E with hn
  obtain ⟨e⟩ := Fintype.truncEquivFin E
  set ψ : Fin n → Bool → ℝ := fun y => φ (e.symm y) with hψ
  have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 (e.symm i) b
  have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 (e.symm i)
  have hAt : IsIncreasing ((cfgEquiv e) ⁻¹' A) := isIncreasing_preimage e hA
  have hBt : IsIncreasing ((cfgEquiv e) ⁻¹' B) := isIncreasing_preimage e hB
  have hbk := bk_wprob n ψ hψ0 hψ1 ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) hAt hBt
  rw [← preimage_disjointOccurrence e A B] at hbk
  rw [wprob_transfer e φ (disjointOccurrence A B), wprob_transfer e φ A, wprob_transfer e φ B]
  exact hbk






theorem bernoulli_real_eq_wprob [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (S : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real S
      = wprob (fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b}) S := by
  rw [bernoulliProductMeasure.real_eq_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [bernoulliProductMeasure.real_singleton]
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem bk_inequality [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hφ1 : ∀ x, φ x false + φ x true = 1 := by
    intro _
    have h1 : (bernoulliMeasure p hp).real {false} = ((1 - p : ℝ≥0) : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
    have h2 : (bernoulliMeasure p hp).real {true} = (p : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
    simp only [hφ]
    rw [h1, h2, NNReal.coe_sub hp, NNReal.coe_one]
    ring
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact bk_wprob_general φ hφ0 hφ1 hA hB

end StatMech
