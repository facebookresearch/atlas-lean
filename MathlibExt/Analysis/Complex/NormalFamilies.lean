/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Normal families: Montel's and Vitali's theorems

Proves `Wanted` entries `montel` and `vitali`.
-/

@[expose] public section

open Set Filter Topology

namespace MathlibExt.Analysis.Complex.NormalFamilies

/-- Local uniform boundedness of `F` on `U`: every `x ∈ U` has neighbourhood `V ⊆ U`
and `C ≥ 0` with `‖F n y‖ ≤ C` for all `n` and `y ∈ V`. -/
def IsLocallyUniformlyBoundedOn (U : Set ℂ) (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ V, ‖F n y‖ ≤ C

/-- A family bounded by `C` on an open set is locally uniformly bounded there. -/
theorem isLocallyUniformlyBoundedOn_of_forall_norm_le {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hF : ∀ n, ∀ y ∈ U, ‖F n y‖ ≤ C) :
    IsLocallyUniformlyBoundedOn U F :=
  fun _ hx => ⟨U, hU, hx, subset_rfl, C, hC, hF⟩

/-- A locally uniformly bounded family is uniformly bounded on each compact subset. -/
theorem IsLocallyUniformlyBoundedOn.exists_bound_of_isCompact {U : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hB : IsLocallyUniformlyBoundedOn U F)
    {K : Set ℂ} (hKU : K ⊆ U) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ K, ‖F n y‖ ≤ C := by
  have h1 : ∀ x : K, ∃ V : Set ℂ, IsOpen V ∧ (x : ℂ) ∈ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ V, ‖F n y‖ ≤ C := by
    intro x
    obtain ⟨V, hVo, hxV, -, C, hC0, hC⟩ := hB (x : ℂ) (hKU x.property)
    exact ⟨V, hVo, hxV, C, hC0, hC⟩
  choose V hV using h1
  choose C hC using (fun x => (hV x).2.2)
  have hcover : K ⊆ ⋃ i, V i := by
    intro x hx
    rw [Set.mem_iUnion]
    exact ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun i : K => V i) (fun i => (hV i).1) hcover
  by_cases hKne : K.Nonempty
  · have htne : t.Nonempty := by
      obtain ⟨x0, hx0⟩ := hKne
      have hx0' := ht hx0
      rw [Set.mem_iUnion] at hx0'
      obtain ⟨i, hi⟩ := hx0'
      rw [Set.mem_iUnion] at hi
      obtain ⟨himem, -⟩ := hi
      exact ⟨i, himem⟩
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image t C htne
    refine ⟨C i0, (hC i0).1, fun n y hy => ?_⟩
    have hy' := ht hy
    rw [Set.mem_iUnion] at hy'
    obtain ⟨i, hi⟩ := hy'
    rw [Set.mem_iUnion] at hi
    obtain ⟨himem, hyi⟩ := hi
    exact le_trans ((hC i).2 n y hyi) (hmax i himem)
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    exact ⟨0, le_rfl, fun n y hy => by simp [hKne] at hy⟩

/-- Every point of an open set lies in a small ball about a dense point whose closed
hull of double radius stays inside the open set. -/
private lemma mem_disc {U : Set ℂ} (hU : IsOpen U) {D : Set ℂ} (hDdense : Dense D)
    {x : ℂ} (hxU : x ∈ U) :
    ∃ q : ℂ, ∃ k : ℕ, q ∈ D ∧ 1 ≤ k ∧ Metric.closedBall q ((((k : ℝ)))⁻¹) ⊆ U ∧
      x ∈ Metric.ball q ((((k : ℝ))⁻¹) / 4) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < ε / 2)
  set k : ℕ := n + 1 with hk_def
  have hk1 : 1 ≤ k := Nat.le_add_left 1 n
  have hkn : ((k : ℝ)) = (n : ℝ) + 1 := by rw [hk_def, Nat.cast_add, Nat.cast_one]
  set s : ℝ := (((k : ℝ)))⁻¹ with hs_def
  have hks : (0 : ℝ) < (k : ℝ) := by
    rw [hkn]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hspos : (0 : ℝ) < s := inv_pos.mpr hks
  have hsε : s < ε / 2 := by
    rw [hs_def, hkn, inv_eq_one_div]
    exact hn
  set δ : ℝ := min (ε / 2) (s / 8) with hδ_def
  have hδ : (0 : ℝ) < δ := lt_min (by linarith) (by linarith)
  obtain ⟨q, hqx, hqD⟩ :=
    Dense.inter_open_nonempty hDdense (Metric.ball x δ) Metric.isOpen_ball
      ⟨x, Metric.mem_ball_self hδ⟩
  have hdist : dist q x < δ := Metric.mem_ball.mp hqx
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ s / 8 := min_le_right _ _
  refine ⟨q, k, hqD, hk1, ?_, ?_⟩
  · intro w hw
    rw [Metric.mem_closedBall] at hw
    apply hball
    rw [Metric.mem_ball]
    have htri := dist_triangle w q x
    linarith [hw, hdist, hδ1, hδ2, hsε]
  · rw [Metric.mem_ball, dist_comm]
    linarith [hdist, hδ2]

/-- Arzelà–Ascoli subsequence on a closed disc, given a uniform bound on a larger disc. -/
private lemma disc_subseq {U : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    {c : ℂ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall c ρ ⊆ U)
    (hC0 : 0 ≤ C) (hC : ∀ n, ∀ y ∈ Metric.closedBall c ρ, ‖F n y‖ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun m => F (σ m)) g atTop (Metric.closedBall c (ρ / 4)) := by
  classical
  set D : Set ℂ := Metric.ball c (ρ / 2) with hD_def
  set L : ℝ := C / (ρ / 2) with hL_def
  have hρ2 : (0 : ℝ) < ρ / 2 := by linarith
  have hL0 : (0 : ℝ) ≤ L := div_nonneg hC0 (le_of_lt hρ2)
  have hDU : D ⊆ U :=
    (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ))).trans hsub
  have hdiff : ∀ n, DifferentiableOn ℂ (F n) D := fun n => (hF n).mono hDU
  have hderiv : ∀ n, ∀ z ∈ D, ‖deriv (F n) z‖ ≤ L := by
    intro n z hz
    rw [hD_def, Metric.mem_ball] at hz
    have hsph : ∀ w ∈ Metric.sphere z (ρ / 2), ‖F n w‖ ≤ C := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      apply hC n w
      rw [Metric.mem_closedBall]
      have htri := dist_triangle w z c
      linarith [hw, hz]
    have hcb : Metric.closedBall z (ρ / 2) ⊆ U := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      apply hsub
      rw [Metric.mem_closedBall]
      have htri := dist_triangle w z c
      linarith [hw, hz]
    have hdc : DiffContOnCl ℂ (F n) (Metric.ball z (ρ / 2)) :=
      (hF n).diffContOnCl_ball hcb
    have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ2 hdc hsph
    rwa [hL_def]
  have hlip : ∀ n, LipschitzOnWith (NNReal.mk L hL0) (F n) D := by
    intro n
    apply (convex_ball c (ρ / 2)).lipschitzOnWith_of_nnnorm_derivWithin_le (hdiff n)
    intro z hz
    have hmem : D ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
    have hle := hderiv n z hz
    rw [derivWithin_of_mem_nhds hmem]
    exact_mod_cast hle
  set K' : Set ℂ := Metric.closedBall c (ρ / 4) with hK'_def
  have hKR : K' ⊆ Metric.closedBall c ρ :=
    Metric.closedBall_subset_closedBall (by linarith : ρ / 4 ≤ ρ)
  have hK'U : K' ⊆ U := hKR.trans hsub
  have hK'D : K' ⊆ D := by
    intro y hy
    have hy' : y ∈ Metric.closedBall c (ρ / 4) := hy
    rw [Metric.mem_closedBall] at hy'
    rw [hD_def, Metric.mem_ball]
    linarith [hy']
  have hcompact : CompactSpace K' :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall c (ρ / 4))
  have hcont : ∀ n, Continuous (K'.domRestrict (F n)) := by
    intro n
    rw [← continuousOn_iff_continuous_domRestrict]
    exact ((hF n).continuousOn.mono hK'U)
  have hmem : ∀ n, ∀ x : K', ‖F n (x : ℂ)‖ ≤ C := fun n x => hC n _ (hKR x.property)
  have hbd : ∀ n, ∀ x y : K', dist (F n (x : ℂ)) (F n (y : ℂ)) ≤ 2 * C := by
    intro n x y
    calc dist (F n (x : ℂ)) (F n (y : ℂ))
        ≤ ‖F n (x : ℂ)‖ + ‖F n (y : ℂ)‖ := dist_le_norm_add_norm _ _
      _ ≤ C + C := add_le_add (hmem n x) (hmem n y)
      _ = 2 * C := by ring
  set G : ℕ → BoundedContinuousFunction K' ℂ := fun n =>
    BoundedContinuousFunction.mkOfBound ⟨K'.domRestrict (F n), hcont n⟩ (2 * C)
      (hbd n) with hG_def
  set A : Set (BoundedContinuousFunction K' ℂ) := Set.range G with hA_def
  set S : Set ℂ := Metric.closedBall 0 C with hS_def
  have hS : IsCompact S := isCompact_closedBall 0 C
  have hAS : ∀ f : BoundedContinuousFunction K' ℂ, ∀ x : K', f ∈ A → f x ∈ S := by
    intro f x hf
    obtain ⟨n, rfl⟩ := hf
    rw [hS_def, Metric.mem_closedBall, dist_zero_right]
    exact hmem n x
  have hE : Equicontinuous
      (fun (x : A) => ⇑(x : BoundedContinuousFunction K' ℂ)) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun t => L * t) ?_ _ ?_
    · have hLc : Continuous (fun t : ℝ => L * t) := continuous_const.mul continuous_id'
      have h0 := hLc.tendsto (0 : ℝ)
      simpa using h0
    · intro y₁ y₂ f
      obtain ⟨n, hn⟩ := f.property
      rw [← hn]
      have hy₁ : ((y₁ : K') : ℂ) ∈ D := hK'D y₁.property
      have hy₂ : ((y₂ : K') : ℂ) ∈ D := hK'D y₂.property
      have hed := (hlip n) hy₁ hy₂
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk,
        ← ENNReal.ofReal_mul hL0] at hed
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL0 dist_nonneg)).mp hed
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli S hS A hAS hE
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ, (fun x => if h : x ∈ K' then a ⟨x, h⟩ else 0), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  filter_upwards [eventually_atTop.mpr ⟨N, hN⟩] with m hm x hx
  rw [dite_eq_left hx]
  have hle :=
    BoundedContinuousFunction.dist_coe_le_dist (f := G (φ m)) (g := a)
      (⟨x, hx⟩ : K')
  have hm' : dist (G (φ m)) a < ε := hm
  calc dist (a ⟨x, hx⟩) (F (φ m) x)
      = dist (a ⟨x, hx⟩) ((G (φ m)) ⟨x, hx⟩) := rfl
    _ = dist ((G (φ m)) ⟨x, hx⟩) (a ⟨x, hx⟩) := dist_comm _ _
    _ ≤ dist (G (φ m)) a := hle
    _ < ε := hm'

/--
Let `U` be open and `F : ℕ → ℂ → ℂ` holomorphic on `U` and locally uniformly bounded on `U`. Then
some strictly monotone subsequence converges locally uniformly on `U` to holomorphic `f`. Source:
Montel's theorem on normal families, P. Montel 1912/1927; see Ahlfors, Functions of One Complex
Variable II; Lean is locally uniformly bounded holomorphic family with strictly monotone
subsequence locally uniform convergent to holomorphic limit, open U form.
Proves `Wanted` entry `montel`.
-/
theorem montel
    {U : Set ℂ} (hU : IsOpen U)
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hB : IsLocallyUniformlyBoundedOn U F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop U := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  set S : Set (ℂ × ℕ) :=
    {p | p.1 ∈ D ∧ 1 ≤ p.2 ∧ Metric.closedBall p.1 ((((p.2 : ℝ)))⁻¹) ⊆ U} with hS_def
  have hScount : S.Countable :=
    Set.Countable.mono (s₁ := S)
      (fun (p : ℂ × ℕ) (hp : p ∈ S) => Set.mk_mem_prod hp.1 (Set.mem_univ _))
      (hDcount.prod Set.countable_univ)
  have hJcount : Countable ↥S := hScount.to_subtype
  by_cases hJne : Nonempty ↥S
  · have := hJcount
    have := hJne
    obtain ⟨e, he⟩ := exists_surjective_nat ↥S
    set Kj : ℕ → Set ℂ := fun j =>
      Metric.closedBall (e j).val.1 (((((e j).val.2 : ℝ)))⁻¹ / 4) with hKj_def
    have hstep : ∀ j (τ : ℕ → ℕ), ∃ p : (ℕ → ℕ) × (ℂ → ℂ),
        (StrictMono τ → ∃ σ : ℕ → ℕ, StrictMono σ ∧ p.1 = τ ∘ σ) ∧
        (StrictMono τ → StrictMono p.1) ∧
        (StrictMono τ →
          TendstoUniformlyOn (fun m => F (p.1 m)) p.2 atTop (Kj j)) := by
      intro j τ
      obtain ⟨-, hk1, hsub⟩ := (e j).property
      have hkpos : (0 : ℝ) < (((e j).val.2 : ℝ)) :=
        Nat.cast_pos.mpr (by omega)
      have hρ : (0 : ℝ) < ((((e j).val.2 : ℝ)))⁻¹ := inv_pos.mpr hkpos
      obtain ⟨C, hC0, hCb⟩ := hB.exists_bound_of_isCompact hsub (isCompact_closedBall _ _)
      have hF' : ∀ m, DifferentiableOn ℂ (F (τ m)) U := fun m => hF (τ m)
      obtain ⟨σ, hσ, g, hg⟩ := disc_subseq hF' hρ hsub hC0
        (fun n y hy => hCb (τ n) y hy)
      exact ⟨(τ ∘ σ, g), (fun _ => ⟨σ, hσ, rfl⟩), (fun hτ => hτ.comp hσ),
        (fun _ => hg)⟩
    choose ext hext using hstep
    have hτdef : ∃ τ : ℕ → (ℕ → ℕ),
        τ 0 = (ext 0 id).1 ∧ ∀ j, τ (j + 1) = (ext (j + 1) (τ j)).1 := by
      refine ⟨fun j => Nat.rec (motive := fun _ => ℕ → ℕ) (ext 0 id).1
        (fun j τprev => (ext (j + 1) τprev).1) j, rfl, fun j => rfl⟩
    obtain ⟨τ, hτ0, hτS⟩ := hτdef
    have hmono : ∀ j, StrictMono (τ j) := by
      intro j
      induction j with
      | zero => rw [hτ0]; exact ((hext 0 id).2.1) strictMono_id
      | succ j ih => rw [hτS j]; exact ((hext (j + 1) (τ j)).2.1) ih
    have hnest : ∀ j, ∃ σ : ℕ → ℕ, StrictMono σ ∧ τ (j + 1) = τ j ∘ σ := by
      intro j
      rw [hτS j]
      exact ((hext (j + 1) (τ j)).1) (hmono j)
    have hconv : ∀ j, ∃ g : ℂ → ℂ,
        TendstoUniformlyOn (fun m => F (τ j m)) g atTop (Kj j) := by
      intro j
      rcases j with _ | j
      · rw [hτ0]
        exact ⟨(ext 0 id).2, ((hext 0 id).2.2) strictMono_id⟩
      · rw [hτS j]
        exact ⟨(ext (j + 1) (τ j)).2, ((hext (j + 1) (τ j)).2.2) (hmono j)⟩
    choose g hg using hconv
    set ψ : ℕ → ℕ := fun m => τ m m with hψ_def
    have hcomp : ∀ a b, a ≤ b → ∃ T : ℕ → ℕ, StrictMono T ∧ τ b = τ a ∘ T := by
      intro a b h
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      clear h
      induction k with
      | zero => exact ⟨id, strictMono_id, by simp⟩
      | succ k ih =>
        obtain ⟨T, hT, hTeq⟩ := ih
        obtain ⟨σ, hσ, hσeq⟩ := hnest (a + k)
        refine ⟨T ∘ σ, hT.comp hσ, ?_⟩
        have hab : a + (k + 1) = (a + k) + 1 := by ring
        rw [hab, hσeq, hTeq, Function.comp_assoc]
    have hψ : StrictMono ψ := by
      intro a b hab
      obtain ⟨T, hT, hTeq⟩ := hcomp a b (le_of_lt hab)
      have hlt : a < T b := lt_of_lt_of_le hab (hT.le_apply)
      change τ a a < τ b b
      rw [hTeq]
      change τ a a < τ a (T b)
      exact (hmono a) hlt
    have hUj : ∀ j, TendstoUniformlyOn (fun m => F (ψ m)) (g j) atTop (Kj j) := by
      intro j
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hgj := (Metric.tendstoUniformlyOn_iff.mp (hg j)) ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp hgj
      refine eventually_atTop.mpr ⟨max N j, fun m hm x hx => ?_⟩
      have hmN : N ≤ m := le_trans (le_max_left N j) hm
      have hmj : j ≤ m := le_trans (le_max_right N j) hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmj
      obtain ⟨T, hT, hTeq⟩ := hcomp j (j + k) (Nat.le_add_right j k)
      have htN : N ≤ T (j + k) := le_trans hmN (hT.le_apply)
      have eψ : ψ (j + k) = τ j (T (j + k)) := by
        rw [hψ_def]
        change τ (j + k) (j + k) = τ j (T (j + k))
        rw [hTeq, Function.comp_apply]
      rw [eψ]
      exact hN _ htN x hx
    have hcons : ∀ i k x, x ∈ Kj i → x ∈ Kj k → g i x = g k x := by
      intro i k x hxi hxk
      have h1 := (hUj i).tendsto_at hxi
      have h2 := (hUj k).tendsto_at hxk
      exact tendsto_nhds_unique h1 h2
    have hcover : ∀ x ∈ U, ∃ j,
        x ∈ Metric.ball (e j).val.1 (((((e j).val.2 : ℝ)))⁻¹ / 4) := by
      intro x hxU
      obtain ⟨q, k, hqD, hk1, hsub, hxb⟩ := mem_disc hU hDdense hxU
      have hmem : ((q, k) : ℂ × ℕ) ∈ S := by
        change q ∈ D ∧ 1 ≤ k ∧ Metric.closedBall q ((((k : ℝ)))⁻¹) ⊆ U
        exact ⟨hqD, hk1, hsub⟩
      obtain ⟨j, hjj⟩ := he ⟨(q, k), hmem⟩
      refine ⟨j, ?_⟩
      rw [hjj]
      exact hxb
    set f : ℂ → ℂ := fun x =>
      if h : ∃ j, x ∈ Kj j then g (Classical.choose h) x else 0 with hf_def
    have hfK : ∀ j, TendstoUniformlyOn (fun m => F (ψ m)) f atTop (Kj j) := by
      intro j
      apply (hUj j).congr_right
      intro x hx
      show g j x = f x
      have hex : (∃ j, x ∈ Kj j) := ⟨j, hx⟩
      simp only [hf_def]
      rw [dite_eq_left hex]
      have hxc : x ∈ Kj (Classical.choose hex) := Classical.choose_spec hex
      exact hcons j _ x hx hxc
    have hTLU : TendstoLocallyUniformlyOn (fun m => F (ψ m)) f atTop U := by
      apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
      intro x hxU
      obtain ⟨j, hjx⟩ := hcover x hxU
      exact ⟨Metric.ball (e j).val.1 (((((e j).val.2 : ℝ)))⁻¹ / 4),
        mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hjx),
        (hfK j).mono Metric.ball_subset_closedBall⟩
    have hdiff : DifferentiableOn ℂ f U :=
      hTLU.differentiableOn (Filter.Eventually.of_forall fun m => hF (ψ m)) hU
    exact ⟨ψ, hψ, f, hdiff, hTLU⟩
  · have hUempty : U = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hxU
      obtain ⟨q, k, hqD, hk1, hsub, hxb⟩ := mem_disc hU hDdense hxU
      have hmem : ((q, k) : ℂ × ℕ) ∈ S := by
        change q ∈ D ∧ 1 ≤ k ∧ Metric.closedBall q ((((k : ℝ)))⁻¹) ⊆ U
        exact ⟨hqD, hk1, hsub⟩
      exact hJne ⟨⟨(q, k), hmem⟩⟩
    subst hUempty
    refine ⟨id, strictMono_id, fun _ => 0, differentiableOn_empty, ?_⟩
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro x hx
    exact absurd hx (Set.notMem_empty x)

/-- From `∀ N, ∃ n ≥ N, P n`, extract a strictly monotone subsequence
along which `P` always holds. -/
private lemma strictMono_subseq_of_forall_exists {P : ℕ → Prop}
    (h : ∀ N, ∃ n, N ≤ n ∧ P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  choose ψ hψ using h
  let φ : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (ψ 0) (fun _ ih => ψ (ih + 1)) n
  have hφ0 : φ 0 = ψ 0 := rfl
  have hφS : ∀ n, φ (n + 1) = ψ (φ n + 1) := fun n => rfl
  have hP : ∀ n, P (φ n) := by
    intro n
    induction n with
    | zero => rw [hφ0]; exact (hψ 0).2
    | succ n ih => rw [hφS]; exact (hψ _).2
  have hlt : ∀ n, φ n < φ (n + 1) := by
    intro n
    rw [hφS]
    have h1 := (hψ (φ n + 1)).1
    linarith
  exact ⟨φ, strictMono_nat_of_lt_succ hlt, hP⟩

/-- Two holomorphic functions agreeing on `S` (which accumulates in `U`)
agree on all of the preconnected open set `U`. -/
private lemma eqOn_of_agree_on_S
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f f' : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf' : DifferentiableOn ℂ f' U)
    {S : Set ℂ} {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hacc : AccPt x₀ (𝓟 S))
    (hff' : ∀ z ∈ S, f z = f' z) :
    Set.EqOn f f' U := by
  apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (hf.analyticOnNhd hU) (hf'.analyticOnNhd hU) hUc hx₀
  have hfreq : ∃ᶠ y in 𝓝[≠] x₀, y ∈ S := accPt_iff_frequently_nhdsNE.mp hacc
  exact hfreq.mono (fun y hy => hff' y hy)

/--
Let `U` be open preconnected, `F` holomorphic on `U` and locally uniformly bounded, and `S ⊆ U`
accumulate at some `x₀ ∈ U`. If `Fₙ → g` pointwise on `S`, then `F` converges locally uniformly on
`U` to holomorphic `f` extending `g` on `S`. Source: Vitali convergence theorem, G. Vitali 1903;
see Hille, Analytic Function Theory Vol II and Conway II; Lean is open preconnected U locally
uniformly bounded with AccPt accumulation and pointwise limit on S extends to locally uniform
holomorphic convergence, Montel-related strengthening.
Proves `Wanted` entry `vitali`.
-/
theorem vitali
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (F : ℕ → ℂ → ℂ) (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hB : IsLocallyUniformlyBoundedOn U F)
    {S : Set ℂ} (hS : S ⊆ U) (hAcc : ∃ x₀ ∈ U, AccPt x₀ (𝓟 S))
    (g : ℂ → ℂ) (hg : ∀ z ∈ S, Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ (∀ z ∈ S, f z = g z) ∧
      TendstoLocallyUniformlyOn F f atTop U := by
  obtain ⟨x₀, hx₀U, hx₀acc⟩ := hAcc
  -- One subsequential limit `f₀`, holomorphic, extending `g`.
  obtain ⟨φ₀, hφ₀, f₀, hf₀diff, hf₀tluo⟩ := montel hU F hF hB
  have hf₀g : ∀ z ∈ S, f₀ z = g z := by
    intro z hz
    have h1 : Tendsto (fun j => F (φ₀ j) z) atTop (𝓝 (f₀ z)) :=
      hf₀tluo.tendsto_at (hS hz)
    have h2 : Tendsto (fun j => F (φ₀ j) z) atTop (𝓝 (g z)) :=
      (hg z hz).comp hφ₀.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  -- The whole sequence converges to `f₀`: argue compact by compact.
  have hfull : TendstoLocallyUniformlyOn F f₀ atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    by_contra hnot
    rw [Metric.tendstoUniformlyOn_iff] at hnot
    have hbad : ∃ ε > 0, ∃ᶠ n in atTop, ∃ x ∈ K, ε ≤ dist (f₀ x) (F n x) := by
      by_contra hc
      push Not at hc
      exact hnot hc
    obtain ⟨ε, hε, hfreq⟩ := hbad
    have hN : ∀ N, ∃ n, N ≤ n ∧ ∃ x ∈ K, ε ≤ dist (f₀ x) (F n x) := by
      intro N
      obtain ⟨b, hb, hbx⟩ := Filter.frequently_atTop.mp hfreq N
      obtain ⟨x, hxk, hdist⟩ := hbx
      exact ⟨b, hb, x, hxk, hdist⟩
    obtain ⟨φ₁, hφ₁, hP⟩ := strictMono_subseq_of_forall_exists hN
    choose x hx using hP
    have hH : ∀ n, DifferentiableOn ℂ ((fun k => F (φ₁ k)) n) U := fun n => hF (φ₁ n)
    have hHB : IsLocallyUniformlyBoundedOn U (fun k => F (φ₁ k)) := by
      intro y hy
      obtain ⟨V, hVo, hym, hVU, C, hC0, hC⟩ := hB y hy
      exact ⟨V, hVo, hym, hVU, C, hC0, fun n => hC (φ₁ n)⟩
    obtain ⟨φ₂, hφ₂, f₁, hf₁diff, hf₁tluo⟩ := montel hU _ hH hHB
    have hf₁g : ∀ z ∈ S, f₁ z = g z := by
      intro z hz
      have h1 : Tendsto (fun j => F (φ₁ (φ₂ j)) z) atTop (𝓝 (f₁ z)) :=
        hf₁tluo.tendsto_at (hS hz)
      have h2 : Tendsto (fun j => F (φ₁ (φ₂ j)) z) atTop (𝓝 (g z)) :=
        (hg z hz).comp (hφ₁.comp hφ₂).tendsto_atTop
      exact tendsto_nhds_unique h1 h2
    have hEq : Set.EqOn f₁ f₀ U :=
      eqOn_of_agree_on_S hU hUc hf₁diff hf₀diff hx₀U hx₀acc
        (fun z hz => (hf₁g z hz).trans (hf₀g z hz).symm)
    have huni : TendstoUniformlyOn (fun j => F ((φ₁ ∘ φ₂) j)) f₁ atTop K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf₁tluo K hKU hK
    rw [Metric.tendstoUniformlyOn_iff] at huni
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (huni ε hε)
    have hkk := hN N le_rfl (x (φ₂ N)) (hx (φ₂ N)).1
    have heqpt : f₁ (x (φ₂ N)) = f₀ (x (φ₂ N)) := hEq (hKU (hx (φ₂ N)).1)
    have hbadpt := (hx (φ₂ N)).2
    have hcomp : (φ₁ ∘ φ₂) N = φ₁ (φ₂ N) := rfl
    rw [heqpt, hcomp] at hkk
    linarith
  exact ⟨f₀, hf₀diff, hf₀g, hfull⟩

end MathlibExt.Analysis.Complex.NormalFamilies
