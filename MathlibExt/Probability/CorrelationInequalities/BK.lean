/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.DisjointOccurrence
public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

@[expose] public section

/-!
# The van den Berg–Kesten inequality

For a finite set `E` and a product weight on `ConfigSpace E = E → Bool` (independent coordinates,
coordinate `x` open with probability `φ x true`), the probability that two increasing events
occur disjointly is at most the product of their probabilities:
`P(A □ B) ≤ P(A) * P(B)`.

The proof is by induction on the number of coordinates: condition on the first coordinate,
split each event into its two slices, and close the step with an elementary inequality
(`StatMech.bk_algebra`).

## Main definitions

* `StatMech.pweight φ ω = ∏ x, φ x (ω x)`: the product weight of a configuration.
* `StatMech.wprob φ S`: the `pweight φ`-mass of an event `S`. For `φ ≥ 0` and
  `φ x false + φ x true = 1` this is the probability of `S` under the product measure with
  marginals `φ x`.
* `StatMech.slice C x`: the section of an event on `Fin (n + 1)` at first coordinate `x`.
* `StatMech.cfgEquiv e`: the bijection of configuration spaces induced by `e : E ≃ F`.

## Main results

* `StatMech.bk_wprob_general`: the BK inequality for an arbitrary product probability weight on a
  finite set.
* `StatMech.bk_inequality`: the **van den Berg–Kesten inequality** for the product Bernoulli
  measure `bernoulliProductMeasure p`.

## References

* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985).
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 2.3.
-/

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace

variable {E F : Type*}

/-- If an increasing event `A` occurs on `K` at `ω` and `ω ≤ ω'`, then `A` occurs on `K` at
`ω'`. -/
theorem OccursOn.mono_config {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {K : Set E} {omega omega' : ConfigSpace E} (homega : omega ≤ omega')
    (hocc : OccursOn A K omega) : OccursOn A K omega' := by
  classical
  intro z hz
  let z' : ConfigSpace E := fun e => if e ∈ K then omega e else z e
  have hz'A : z' ∈ A := hocc z' (by
    intro e he
    simp [z', he])
  apply hA (b := z) _ hz'A
  intro e
  by_cases he : e ∈ K
  · simp only [z', ite_eq_left he]
    rw [hz e he]
    exact homega e
  · simp only [z', ite_eq_right he]
    exact le_rfl

/-- The disjoint occurrence of two increasing events is increasing. -/
theorem disjointOccurrence_isIncreasing {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    IsIncreasing (disjointOccurrence A B) := by
  intro omega omega' homega
  rintro ⟨K, L, hKL, hAK, hBL⟩
  exact ⟨K, L, hKL, OccursOn.mono_config hA homega hAK,
    OccursOn.mono_config hB homega hBL⟩

/-- The product weight `∏ x, φ x (ω x)` of a configuration `ω`, where `φ x b` is the weight
of value `b` at coordinate `x`. -/
def pweight [Fintype E] (φ : E → Bool → ℝ) (ω : ConfigSpace E) : ℝ := ∏ x, φ x (ω x)

/-- A product of nonnegative coordinate weights is nonnegative. -/
lemma pweight_nonneg [Fintype E] {φ : E → Bool → ℝ} (hφ : ∀ x b, 0 ≤ φ x b)
    (ω : ConfigSpace E) : 0 ≤ pweight φ ω :=
  Finset.prod_nonneg (fun x _ => hφ x (ω x))

/-- The `pweight φ`-mass `∑ ω ∈ S, pweight φ ω` of an event `S`. When `φ ≥ 0` and
`φ x false + φ x true = 1` for all `x`, this is the probability of `S` under the product measure
whose coordinate `x` has law `φ x`. -/
noncomputable def wprob [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (S : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω

/-- `wprob φ` is monotone for nonnegative weights. -/
lemma wprob_mono [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ} (hφ : ∀ x b, 0 ≤ φ x b)
    {S T : Set (ConfigSpace E)} (h : S ⊆ T) : wprob φ S ≤ wprob φ T := by
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right _ (pweight_nonneg hφ ω)
  by_cases hS : ω ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (h hS)]
  · rw [Set.indicator_of_notMem hS]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω

/-- A product probability weight has total mass `1`. -/
lemma sum_pweight_eq_one [Fintype E] [DecidableEq E] {w : E → Bool → ℝ}
    (hw1 : ∀ x, w x false + w x true = 1) :
    (∑ b : ConfigSpace E, pweight w b) = 1 := by
  simp only [pweight]
  rw [← Fintype.prod_sum (fun s => w s)]
  simp only [Fintype.sum_bool]
  exact Finset.prod_eq_one (fun s _ => by rw [add_comm]; exact hw1 s)

/-- Inclusion–exclusion for `wprob`. -/
lemma wprob_union_inter [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (U V : Set (ConfigSpace E)) :
    wprob φ (U ∪ V) + wprob φ (U ∩ V) = wprob φ U + wprob φ V := by
  simp only [wprob, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hU : ω ∈ U <;> by_cases hV : ω ∈ V <;>
    simp [Set.indicator, hU, hV, Set.mem_union, Set.mem_inter_iff]

/-- The scalar inequality behind the induction step of the BK inequality: with `q = 1 - p`,
`p, q ≥ 0`, if `c0 ≤ m ≤ a0 b0`, `c1 ≤ a0 b1 + a1 b0 - m` and `c1 ≤ a1 b1`, then
`q c0 + p c1 ≤ (q a0 + p a1) (q b0 + p b1)`. -/
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

/-- The section of an event `C` on `Fin (n + 1)` at first coordinate `x`: the configurations
`ω'` on `Fin n` with `Fin.cons x ω' ∈ C`. -/
def slice {n : ℕ} (C : Set (ConfigSpace (Fin (n + 1)))) (x : Bool) :
    Set (ConfigSpace (Fin n)) := {ω' | Fin.cons x ω' ∈ C}

/-- The coordinate set `{j | j.succ ∈ K}`: `K` with the first coordinate removed, shifted down. -/
def sliceSet {n : ℕ} (K : Set (Fin (n + 1))) : Set (Fin n) := {j | j.succ ∈ K}

/-- The indicator of `S` at `Fin.cons x ω'` is the indicator of the slice at `ω'`. -/
lemma indicator_slice {n : ℕ} (S : Set (ConfigSpace (Fin (n + 1)))) (x : Bool)
    (ω' : ConfigSpace (Fin n)) :
    S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω')
      = (slice S x).indicator (fun _ => (1 : ℝ)) ω' := rfl

/-- The product weight factors over the first coordinate. -/
lemma pweight_cons {n : ℕ} (φ : Fin (n + 1) → Bool → ℝ) (x : Bool) (ω' : ConfigSpace (Fin n)) :
    pweight φ (Fin.cons x ω') = φ 0 x * pweight (fun j => φ j.succ) ω' := by
  simp only [pweight]
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  exact congrArg _ (Finset.prod_congr rfl (fun j _ => by rw [Fin.cons_succ]))

/-- Conditioning on the first coordinate:
`wprob φ S = φ 0 false * wprob ψ (slice S false) + φ 0 true * wprob ψ (slice S true)`,
where `ψ` is `φ` on the remaining coordinates. -/
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

/-- Slices of an increasing event are increasing. -/
lemma slice_isIncreasing {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))} (hC : IsIncreasing C)
    (x : Bool) : IsIncreasing (slice C x) := by
  intro a b hab ha
  simp only [slice, Set.mem_ofPred_eq] at ha ⊢
  apply hC _ ha
  intro i; refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero]
  · intro j; simp only [Fin.cons_succ]; exact hab j

/-- For an increasing event, the `false` slice is contained in the `true` slice. -/
lemma slice_false_subset_true {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    (hC : IsIncreasing C) : slice C false ⊆ slice C true := by
  intro ω' hω'
  simp only [slice, Set.mem_ofPred_eq] at hω' ⊢
  apply hC _ hω'
  intro i; refine Fin.cases ?_ ?_ i
  · simp [Fin.cons_zero]
  · intro j; simp [Fin.cons_succ]

/-- Occurrence on `K` at `Fin.cons false ω'` passes to the `false` slice. -/
lemma occursOn_slice_of_false {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {ω' : ConfigSpace (Fin n)}
    (h : OccursOn C K (Fin.cons false ω')) :
    OccursOn (slice C false) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_ofPred_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro _; simp [Fin.cons_zero]
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj

/-- Occurrence on `K` at `Fin.cons true ω'` passes to the `true` slice. -/
lemma occursOn_slice_true {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {ω' : ConfigSpace (Fin n)}
    (h : OccursOn C K (Fin.cons true ω')) :
    OccursOn (slice C true) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_ofPred_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro _; simp [Fin.cons_zero]
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj

/-- If the witness set `K` avoids the first coordinate, occurrence on `K` passes to the
`false` slice whatever the value of the first coordinate. -/
lemma occursOn_slice_false_notmem {n : ℕ} {C : Set (ConfigSpace (Fin (n + 1)))}
    {K : Set (Fin (n + 1))} {x : Bool} {ω' : ConfigSpace (Fin n)}
    (h0 : (0 : Fin (n + 1)) ∉ K) (h : OccursOn C K (Fin.cons x ω')) :
    OccursOn (slice C false) (sliceSet K) ω' := by
  intro τ hτ
  simp only [slice, Set.mem_ofPred_eq]
  apply h
  intro i hi; refine Fin.cases ?_ ?_ i hi
  · intro hi0; exact absurd hi0 h0
  · intro j hj; simp only [Fin.cons_succ]; exact hτ j hj

/-- `sliceSet` preserves disjointness. -/
lemma sliceSet_disjoint {n : ℕ} {K L : Set (Fin (n + 1))} (h : Disjoint K L) :
    Disjoint (sliceSet K) (sliceSet L) := by
  rw [Set.disjoint_left] at h ⊢
  intro j hjK hjL
  exact h (a := j.succ) hjK hjL

/-- The `false` slice of `A □ B` is contained in the disjoint occurrence of the `false`
slices. -/
theorem slice_disjointOccurrence_false {n : ℕ} {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) false ⊆
      disjointOccurrence (slice A false) (slice B false) := by
  intro ω' hω'
  simp only [slice, Set.mem_ofPred_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
    occursOn_slice_of_false hA, occursOn_slice_of_false hB⟩

/-- The `true` slice of `A □ B` is contained in `(A₀ □ B₁) ∪ (A₁ □ B₀)`, where `A₀, A₁` are
the slices of `A` (similarly for `B`): the first coordinate is used by at most one witness. -/
theorem slice_disjointOccurrence_true {n : ℕ} {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) true ⊆
      disjointOccurrence (slice A false) (slice B true) ∪
      disjointOccurrence (slice A true) (slice B false) := by
  intro ω' hω'
  simp only [slice, Set.mem_ofPred_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  by_cases h0K : (0 : Fin (n + 1)) ∈ K
  · have h0L : (0 : Fin (n + 1)) ∉ L := by rw [Set.disjoint_left] at hKL; exact hKL h0K
    right
    exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
      occursOn_slice_true hA, occursOn_slice_false_notmem h0L hB⟩
  · left
    exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
      occursOn_slice_false_notmem h0K hA, occursOn_slice_true hB⟩

/-- On a one-point configuration space, `OccursOn A K ω` reduces to `ω ∈ A`. -/
lemma occursOn_subsingleton {n : ℕ} [Subsingleton (ConfigSpace (Fin n))]
    {A : Set (ConfigSpace (Fin n))} {K : Set (Fin n)} {ω : ConfigSpace (Fin n)} :
    OccursOn A K ω ↔ ω ∈ A := by
  refine ⟨OccursOn.mem_self, fun h ω' _ => ?_⟩
  rwa [Subsingleton.elim ω' ω]

/-- On a one-point configuration space, `A □ B = A ∩ B`. -/
lemma disjointOccurrence_subsingleton {n : ℕ} [Subsingleton (ConfigSpace (Fin n))]
    (A B : Set (ConfigSpace (Fin n))) :
    disjointOccurrence A B = A ∩ B := by
  ext ω
  rw [mem_disjointOccurrence]
  refine ⟨fun ⟨_, _, _, hA, hB⟩ => ⟨occursOn_subsingleton.mp hA, occursOn_subsingleton.mp hB⟩,
    fun ⟨hA, hB⟩ => ⟨∅, ∅, by simp, occursOn_subsingleton.mpr hA, occursOn_subsingleton.mpr hB⟩⟩

/-- The BK inequality on `Fin n` for a product probability weight `φ`:
`wprob φ (A □ B) ≤ wprob φ A * wprob φ B` for increasing `A, B`. -/
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

/-- The bijection `ω ↦ ω ∘ e` from configurations on `F` to configurations on `E` induced by
`e : E ≃ F`. This is `e.symm.arrowCongr (Equiv.refl Bool)` (`StatMech.cfgEquiv_eq_arrowCongr`). -/
def cfgEquiv (e : E ≃ F) : ConfigSpace F ≃ ConfigSpace E where
  toFun ω := fun x => ω (e x)
  invFun ω := fun y => ω (e.symm y)
  left_inv ω := by funext y; simp
  right_inv ω := by funext x; simp

@[simp] lemma cfgEquiv_apply (e : E ≃ F) (ω : ConfigSpace F) (x : E) :
    cfgEquiv e ω x = ω (e x) := rfl

/-- `cfgEquiv e` agrees with Mathlib's `Equiv.arrowCongr`. -/
lemma cfgEquiv_eq_arrowCongr (e : E ≃ F) :
    cfgEquiv e = e.symm.arrowCongr (Equiv.refl Bool) := by
  ext ω x
  rfl

/-- `cfgEquiv e` is monotone. -/
lemma cfgEquiv_mono (e : E ≃ F) {ω ω' : ConfigSpace F} (h : ω ≤ ω') :
    cfgEquiv e ω ≤ cfgEquiv e ω' := fun x => h (e x)

/-- Agreement on `e '' K` corresponds to agreement on `K` after transport by `cfgEquiv e`. -/
lemma agreeOn_cfgEquiv (e : E ≃ F) (K : Set E) (ωf ωf' : ConfigSpace F) :
    agreeOn (e '' K) ωf ωf' ↔ agreeOn K (cfgEquiv e ωf) (cfgEquiv e ωf') := by
  constructor
  · intro h x hx; simp only [cfgEquiv_apply]; exact h (e x) ⟨x, hx, rfl⟩
  · intro h y hy; obtain ⟨x, hx, rfl⟩ := hy; have := h x hx; simpa using this

/-- Occurrence is preserved by relabeling the coordinates. -/
lemma occursOn_cfgEquiv (e : E ≃ F) (A : Set (ConfigSpace E)) (K : Set E) (ωf : ConfigSpace F) :
    OccursOn ((cfgEquiv e) ⁻¹' A) (e '' K) ωf ↔ OccursOn A K (cfgEquiv e ωf) := by
  constructor
  · intro h ωe hωe
    have hsurj : ωe = cfgEquiv e ((cfgEquiv e).symm ωe) := ((cfgEquiv e).apply_symm_apply ωe).symm
    rw [hsurj]
    refine h _ ?_
    rw [agreeOn_cfgEquiv, (cfgEquiv e).apply_symm_apply ωe]; exact hωe
  · intro h ωf' hωf'; rw [agreeOn_cfgEquiv] at hωf'; exact h _ hωf'

/-- Disjoint occurrence commutes with relabeling the coordinates. -/
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

/-- The product weight is invariant under relabeling the coordinates. -/
lemma pweight_transfer [Fintype E] [Fintype F] (e : E ≃ F) (φ : E → Bool → ℝ)
    (ωf : ConfigSpace F) :
    pweight φ (cfgEquiv e ωf) = pweight (fun y => φ (e.symm y)) ωf := by
  simp only [pweight, cfgEquiv_apply]
  exact Fintype.prod_equiv e (fun x => φ x (ωf (e x))) (fun y => φ (e.symm y) (ωf y))
    (fun x => by simp)

/-- `wprob` is invariant under relabeling the coordinates. -/
lemma wprob_transfer [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E ≃ F) (φ : E → Bool → ℝ) (S : Set (ConfigSpace E)) :
    wprob φ S = wprob (fun y => φ (e.symm y)) ((cfgEquiv e) ⁻¹' S) := by
  simp only [wprob]
  rw [← Equiv.sum_comp (cfgEquiv e) (fun ω => S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω)]
  apply Finset.sum_congr rfl
  intro ωf _
  rw [pweight_transfer]
  congr 1

/-- The **BK inequality** for a product probability weight on a finite set `E`: if `φ ≥ 0`
and `φ x false + φ x true = 1` for all `x`, then `wprob φ (A □ B) ≤ wprob φ A * wprob φ B` for
all increasing events `A, B`. -/
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
  have hAt : IsIncreasing ((cfgEquiv e) ⁻¹' A) := hA.preimage fun _ _ => cfgEquiv_mono e
  have hBt : IsIncreasing ((cfgEquiv e) ⁻¹' B) := hB.preimage fun _ _ => cfgEquiv_mono e
  have hbk := bk_wprob n ψ hψ0 hψ1 ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) hAt hBt
  rw [← preimage_disjointOccurrence e A B] at hbk
  rw [wprob_transfer e φ (disjointOccurrence A B), wprob_transfer e φ A, wprob_transfer e φ B]
  exact hbk

/-- The two point masses of the Bernoulli(`p`) measure add up to `1`. -/
lemma bernoulliMeasure_real_false_add_true {p : ℝ≥0} (hp : p ≤ 1) :
    (bernoulliMeasure p hp).real {false} + (bernoulliMeasure p hp).real {true} = 1 := by
  have h1 : (bernoulliMeasure p hp).real {false} = ((1 - p : ℝ≥0) : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
  have h2 : (bernoulliMeasure p hp).real {true} = (p : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
  rw [h1, h2, NNReal.coe_sub hp, NNReal.coe_one]
  ring

/-- The product Bernoulli measure of an event is its `wprob` for the Bernoulli marginals. -/
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
/-- The **van den Berg–Kesten (BK) inequality** (van den Berg and Kesten 1985): under the product
Bernoulli(`p`) measure on a finite configuration space, for increasing events `A` and `B`,
`P_p(A □ B) ≤ P_p(A) * P_p(B)`. -/
theorem bk_inequality [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hφ1 : ∀ x, φ x false + φ x true = 1 := fun _ => bernoulliMeasure_real_false_add_true hp
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact bk_wprob_general φ hφ0 hφ1 hA hB

end StatMech
