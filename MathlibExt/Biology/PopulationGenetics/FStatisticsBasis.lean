/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Sym.Card

/-!
# The basis theorem for f-statistics

Patterson et al. (2012, section "Admixture graph fitting") remark that for `n` populations

1. the f-statistics (`f2`, `f3` and `f4`) span a linear space `V_F` of dimension `n choose 2`;
2. the statistics `f2 Pᵢ Pⱼ`, `i < j`, form a basis of `V_F`;
3. for a fixed population `P₁`, the statistics `f3 P₁ Pᵢ Pⱼ`, `1 < i ≤ j`, form a basis of
   `V_F` (for `i = j` this is `f3 P₁ Pᵢ Pᵢ = f2 P₁ Pᵢ`).

An f-statistic is the expectation of a quadratic function of the vector `x : P → ℝ` of allele
frequencies at one locus: `f4 A B C D = 𝔼[(x A - x B) * (x C - x D)]`. We state the theorem
for these per-locus quadratic functions (`f4Form`, `f2Form`, `f3Form`), as elements of the real
vector space `(P → ℝ) → ℝ`. A statistic is the integral of its form
(`f4_eq_integral_f4Form`), and a linear combination of forms integrates to the same combination
of statistics (`integral_sum_smul_f2Form`); conversely, a relation among the statistics that
holds for every measure holds among the forms, by taking Dirac measures. So the statements
below cover the theoretical (expected) statistics and the empirical statistics averaged over a
common set of loci, as in the paper.

## Main results

* `fSpace`: the span `V_F` of all `f4Form A B C D` (which contains every `f2Form`, `f3Form`).
* `linearIndependent_f2Form`, `span_f2Form`: the `f2` basis (statement 2).
* `linearIndependent_f3Form`, `span_f3Form`: the `f3` basis with base population `o`
  (statement 3).
* `finrank_fSpace`: `dim V_F = n choose 2` (statement 1).
* `integral_sum_smul_f2Form`: a linear combination of forms integrates to the same linear
  combination of `f2` statistics.

## References

* N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck,
  T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.FStatisticsBasis

variable {P : Type*}

/-- The per-locus `f4` form `x ↦ (x A - x B) * (x C - x D)` on frequency vectors `x : P → ℝ`. -/
def f4Form (A B C D : P) : (P → ℝ) → ℝ := fun x => (x A - x B) * (x C - x D)

/-- The per-locus `f2` form `x ↦ (x A - x B) ^ 2`. -/
def f2Form (A B : P) : (P → ℝ) → ℝ := fun x => (x A - x B) ^ 2

/-- The per-locus `f3` form `x ↦ (x C - x A) * (x C - x B)`. -/
def f3Form (C A B : P) : (P → ℝ) → ℝ := f4Form C A C B

/-- `f2Form A B = f4Form A B A B`. -/
theorem f2Form_eq_f4Form (A B : P) : f2Form A B = f4Form A B A B := by
  funext x
  simp [f2Form, f4Form, sq]

/-- The space `V_F` spanned by all per-locus f-statistics (all `f4Form`; `f2Form` and `f3Form`
are special cases). -/
noncomputable def fSpace (P : Type*) : Submodule ℝ ((P → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range fun q : P × P × P × P => f4Form q.1 q.2.1 q.2.2.1 q.2.2.2)

/-- Every `f4Form` lies in `V_F`. -/
theorem f4Form_mem_fSpace (A B C D : P) : f4Form A B C D ∈ fSpace P :=
  Submodule.subset_span ⟨(A, B, C, D), rfl⟩

/-- Every `f2Form` lies in `V_F`. -/
theorem f2Form_mem_fSpace (A B : P) : f2Form A B ∈ fSpace P := by
  rw [f2Form_eq_f4Form]
  exact f4Form_mem_fSpace A B A B

/-- Every `f3Form` lies in `V_F`. -/
theorem f3Form_mem_fSpace (C A B : P) : f3Form C A B ∈ fSpace P :=
  f4Form_mem_fSpace C A C B

/-- The `f4` statistic is the integral of the `f4` form of the frequency vector. -/
theorem f4_eq_integral_f4Form {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (p : P → Ω → ℝ) (A B C D : P) :
    f4 μ p A B C D = ∫ ω, f4Form A B C D (fun X => p X ω) ∂μ := rfl

/-- A linear combination of `f2` forms integrates to the same linear combination of `f2`
statistics, for square-integrable frequencies. -/
theorem integral_sum_smul_f2Form {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {p : P → Ω → ℝ} (hp : ∀ X, MemLp (p X) 2 μ) (s : Finset ι) (c : ι → ℝ) (A B : ι → P) :
    ∫ ω, (∑ i ∈ s, c i • f2Form (A i) (B i)) (fun X => p X ω) ∂μ =
      ∑ i ∈ s, c i * f2 μ p (A i) (B i) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f2Form]
  rw [integral_finsetSum _ fun i _ => (integrable_sub_sq hp (A i) (B i)).const_mul (c i)]
  simp only [integral_const_mul, f2]

/-- `f2Form` is symmetric. -/
theorem f2Form_comm (A B : P) : f2Form A B = f2Form B A := by
  funext x
  simp only [f2Form]
  ring

/-- `f2Form A A = 0`. -/
@[simp] theorem f2Form_self (A : P) : f2Form A A = 0 := by
  funext x
  simp [f2Form]

/-- `f3Form` is symmetric in its last two arguments. -/
theorem f3Form_comm (C A B : P) : f3Form C A B = f3Form C B A := by
  funext x
  simp only [f3Form, f4Form]
  ring

/-- `f3Form C C B = 0`. -/
@[simp] theorem f3Form_self_left (C B : P) : f3Form C C B = 0 := by
  funext x
  simp [f3Form, f4Form]

/-- `f4Form` in terms of `f2Form`: the polarization identity behind `f4_eq_f2`. -/
theorem f4Form_eq (A B C D : P) :
    f4Form A B C D = (1 / 2 : ℝ) • (f2Form A D + f2Form B C - f2Form A C - f2Form B D) := by
  funext x
  simp only [f4Form, f2Form, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- `f2Form` in terms of the `f3` forms with base `o`. -/
theorem f2Form_eq_f3Form (o A B : P) :
    f2Form A B = f3Form o A A + f3Form o B B - (2 : ℝ) • f3Form o A B := by
  funext x
  simp only [f2Form, f3Form, f4Form, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

section Ordered

variable [LinearOrder P]

/-- Patterson's `f2` basis: the forms `f2Form i j`, `i < j`, are linearly independent. -/
theorem linearIndependent_f2Form :
    LinearIndependent ℝ (fun q : {q : P × P // q.1 < q.2} => f2Form q.1.1 q.1.2) := by
  classical
  let e : P → P → ℝ := fun a => Pi.single a 1
  let Φ : ((P → ℝ) → ℝ) →ₗ[ℝ] ({q : P × P // q.1 < q.2} → ℝ) :=
    { toFun := fun F q => (F (e q.1.1) + F (e q.1.2) - F (e q.1.1 + e q.1.2)) / 2
      map_add' := fun F G => by
        funext q
        simp only [Pi.add_apply]
        ring
      map_smul' := fun c F => by
        funext q
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine LinearIndependent.of_comp Φ ?_
  convert Pi.linearIndependent_single_one {q : P × P // q.1 < q.2} ℝ using 1
  funext r q
  obtain ⟨⟨r1, r2⟩, hr⟩ := r
  obtain ⟨⟨q1, q2⟩, hq⟩ := q
  simp only at hr hq
  simp only [Function.comp_apply, Φ, LinearMap.coe_mk, AddHom.coe_mk, f2Form, e,
    Pi.add_apply, Pi.single_apply]
  by_cases h1 : r1 = q1 <;> by_cases h2 : r2 = q2
  · subst h1 h2
    simp [hr.ne, hr.ne']
  · have hne : (⟨(r1, r2), hr⟩ : {q : P × P // q.1 < q.2}) ≠ ⟨(q1, q2), hq⟩ := fun h =>
      h2 (congrArg (fun z : {q : P × P // q.1 < q.2} => z.1.2) h)
    subst h1
    have : r2 ≠ r1 := hr.ne'
    have : q2 ≠ r1 := hq.ne'
    have := Ne.symm h2
    by_cases h3 : r2 = r1 <;> by_cases h4 : r1 = q2 <;> simp_all
  · have hne : (⟨(r1, r2), hr⟩ : {q : P × P // q.1 < q.2}) ≠ ⟨(q1, q2), hq⟩ := fun h =>
      h1 (congrArg (fun z : {q : P × P // q.1 < q.2} => z.1.1) h)
    subst h2
    have : r1 ≠ r2 := hr.ne
    have : q1 ≠ r2 := hq.ne
    have := Ne.symm h1
    by_cases h3 : r2 = q1 <;> by_cases h4 : r1 = r2 <;> simp_all
  · have hne : (⟨(r1, r2), hr⟩ : {q : P × P // q.1 < q.2}) ≠ ⟨(q1, q2), hq⟩ := fun h =>
      h1 (congrArg (fun z : {q : P × P // q.1 < q.2} => z.1.1) h)
    by_cases h3 : r2 = q1 <;> by_cases h4 : r1 = q2
    · subst h3 h4
      exact absurd (hr.trans hq) (lt_irrefl _)
    all_goals
      have := Ne.symm h1
      have := Ne.symm h2
      simp_all

/-- Patterson's `f2` basis: the forms `f2Form i j`, `i < j`, span `V_F`, i.e. every
f-statistic is a linear combination of the `f2 Pᵢ Pⱼ`, `i < j`. -/
theorem span_f2Form :
    Submodule.span ℝ (Set.range fun q : {q : P × P // q.1 < q.2} => f2Form q.1.1 q.1.2) =
      fSpace P := by
  set S := Submodule.span ℝ
    (Set.range fun q : {q : P × P // q.1 < q.2} => f2Form q.1.1 q.1.2)
  have hmem : ∀ A B : P, f2Form A B ∈ S := by
    intro A B
    rcases lt_trichotomy A B with h | h | h
    · exact Submodule.subset_span ⟨⟨(A, B), h⟩, rfl⟩
    · rw [h, f2Form_self]
      exact S.zero_mem
    · rw [f2Form_comm]
      exact Submodule.subset_span ⟨⟨(B, A), h⟩, rfl⟩
  apply le_antisymm
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun q => f2Form_mem_fSpace _ _)
  · refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun q => ?_)
    rw [SetLike.mem_coe, f4Form_eq]
    exact S.smul_mem _ (S.sub_mem (S.sub_mem (S.add_mem (hmem _ _) (hmem _ _)) (hmem _ _))
      (hmem _ _))

/-- Patterson's `f3` basis with base population `o`: the forms `f3Form o i j` with
`i ≤ j`, `i ≠ o`, `j ≠ o` are linearly independent. -/
theorem linearIndependent_f3Form (o : P) :
    LinearIndependent ℝ
      (fun q : {q : P × P // q.1 ≤ q.2 ∧ q.1 ≠ o ∧ q.2 ≠ o} => f3Form o q.1.1 q.1.2) := by
  classical
  let e : P → P → ℝ := fun a => Pi.single a 1
  let Φ : ((P → ℝ) → ℝ) →ₗ[ℝ] ({q : P × P // q.1 ≤ q.2 ∧ q.1 ≠ o ∧ q.2 ≠ o} → ℝ) :=
    { toFun := fun F q => if q.1.1 = q.1.2 then F (e q.1.1) else
        F (e q.1.1 + e q.1.2) - F (e q.1.1) - F (e q.1.2)
      map_add' := fun F G => by
        funext q
        simp only [Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c F => by
        funext q
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
  refine LinearIndependent.of_comp Φ ?_
  convert Pi.linearIndependent_single_one {q : P × P // q.1 ≤ q.2 ∧ q.1 ≠ o ∧ q.2 ≠ o} ℝ
    using 1
  funext r q
  obtain ⟨⟨r1, r2⟩, hr12, hr1, hr2⟩ := r
  obtain ⟨⟨q1, q2⟩, hq12, hq1, hq2⟩ := q
  simp only [Function.comp_apply, Φ, LinearMap.coe_mk, AddHom.coe_mk, f3Form, f4Form, e,
    Pi.add_apply, Pi.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  simp only at hq12 hq1 hq2 hr12
  simp only [Ne.symm hq1, Ne.symm hq2, ite_false, zero_sub, zero_add, neg_mul_neg]
  by_cases hq : q1 = q2
  · subst hq
    simp only [ite_true]
    split_ifs <;> subst_vars <;> simp_all
  · have hlt : q1 < q2 := lt_of_le_of_ne hq12 hq
    simp only [hq, ite_false]
    clear Φ e hr1 hr2 hq1 hq2
    split_ifs <;> subst_vars <;> norm_num <;> first | order | simp_all

/-- Patterson's `f3` basis with base population `o`: the forms `f3Form o i j` with
`i ≤ j`, `i ≠ o`, `j ≠ o` span `V_F`. -/
theorem span_f3Form (o : P) :
    Submodule.span ℝ
        (Set.range fun q : {q : P × P // q.1 ≤ q.2 ∧ q.1 ≠ o ∧ q.2 ≠ o} =>
          f3Form o q.1.1 q.1.2) =
      fSpace P := by
  set S := Submodule.span ℝ
    (Set.range fun q : {q : P × P // q.1 ≤ q.2 ∧ q.1 ≠ o ∧ q.2 ≠ o} => f3Form o q.1.1 q.1.2)
  have hmem3 : ∀ A B : P, f3Form o A B ∈ S := by
    intro A B
    by_cases hA : A = o
    · rw [hA, f3Form_self_left]
      exact S.zero_mem
    by_cases hB : B = o
    · rw [hB, f3Form_comm, f3Form_self_left]
      exact S.zero_mem
    rcases le_total A B with h | h
    · exact Submodule.subset_span ⟨⟨(A, B), h, hA, hB⟩, rfl⟩
    · rw [f3Form_comm]
      exact Submodule.subset_span ⟨⟨(B, A), h, hB, hA⟩, rfl⟩
  have hmem2 : ∀ A B : P, f2Form A B ∈ S := fun A B => by
    rw [f2Form_eq_f3Form o]
    exact S.sub_mem (S.add_mem (hmem3 _ _) (hmem3 _ _)) (S.smul_mem _ (hmem3 _ _))
  apply le_antisymm
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun q => f3Form_mem_fSpace _ _ _)
  · rw [← span_f2Form]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun q => hmem2 _ _)

end Ordered

/-- The f-statistics of `n` populations span a space of dimension `n choose 2`. (A linear order
on the populations, used to index the `f2` basis, is chosen in the proof.) -/
theorem finrank_fSpace [Fintype P] : Module.finrank ℝ (fSpace P) = (Fintype.card P).choose 2 := by
  classical
  let : LinearOrder P := LinearOrder.lift' (Fintype.equivFin P) (Fintype.equivFin P).injective
  rw [← span_f2Form, finrank_span_eq_card linearIndependent_f2Form, ← Sym2.card_subtype_not_diag]
  refine Fintype.card_congr (Equiv.ofBijective
    (fun q => ⟨s(q.1.1, q.1.2), by simpa using q.2.ne⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    simp only [Subtype.mk.injEq, Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (hab.trans hcd) (lt_irrefl _)
  · rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := by simpa using hz
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨⟨(x, y), h⟩, rfl⟩
      · exact ⟨⟨(y, x), h⟩, Subtype.ext Sym2.eq_swap⟩

end MathlibExt.Biology.PopulationGenetics.FStatisticsBasis
