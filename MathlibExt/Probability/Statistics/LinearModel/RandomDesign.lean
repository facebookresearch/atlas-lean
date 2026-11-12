/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference
public import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesisF
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Random-design linear models, conditionally on the design

The fixed-design Gaussian theory (`LinearModel.Sampling`, `LinearModel.Inference`,
`LinearModel.LinearHypothesisF`) is transported to a random design `X : Ω → Matrix m k ℝ` through
one stated conditional hypothesis and nothing else:

* **Conditional Gaussian errors.** In `y = X β + ε` with `σ > 0`, the conditional law of the
  standardized errors `σ⁻¹ ε` given `X` is, `(law X)`-almost surely, the standard Gaussian on
  `ℝ^m`:
  `condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X] Kernel.const _ (Measure.pi fun _ => N(0, 1))`.
  This is equivalent to `ε` being independent of `X` with `σ⁻¹ ε` standard Gaussian
  (`indepFun_hasLaw_of_condDistrib_ae_eq_const`, `condDistrib_ae_eq_const_of_indepFun`).

* **Rank control.** Invertibility of `Xᵀ X` is never assumed for the random design. Every
  conditional statement holds for `(law X)`-a.e. `x` *in the full-rank event*
  `fullRankDesigns m k = {x | IsUnit (xᵀ x)} = {x | rank x = p}`, which is measurable
  (`measurableSet_fullRankDesigns`). On it the residual-maker matrix has rank
  `n - rank x = n - p` (`rank_residualMatrix_eq_card_sub_rank`), the residual degrees of freedom;
  `p < n` is a hypothesis so that they are positive. Unconditional statements either carry the
  factor `P(X full rank)` or assume `Xᵀ X` invertible almost surely (`hfull`).

## Main results

Conditionally on `X = x`, for `(law X)`-a.e. full-rank `x`:

* `ae_condDistrib_olsEstimator`: `β̂ ~ N(β, σ² (xᵀ x)⁻¹)`.
* `ae_condDistrib_rss_div_sq`: `‖y - X β̂‖² / σ² ~ χ²_{n-p}`.
* `ae_condDistrib_tStatistic`, `ae_condDistrib_abs_tStatistic_le`: the contrast `t` statistic is
  `t_{n-p}`, so `P(|T| ≤ c | X = x) = t_{n-p}([-c, c])`.
* `ae_condDistrib_fStatistic`: under `C β = c` with `rank C = q > 0`, the `F` statistic is
  `F(q, n - p)`; `C (xᵀ x)⁻¹ Cᵀ` is invertible on the full-rank event (`isUnit_hypothesisGram`).

Integrated over the design:

* `measureReal_tStatistic_mem_inter`, `measureReal_fStatistic_mem_inter`:
  `P(X full rank, T ∈ S) = P(X full rank) · t_{n-p}(S)`, and likewise for `F`.
* `measureReal_abs_tStatistic_le_of_ae_fullRank`, `measureReal_fStatistic_mem_of_ae_fullRank`:
  if `Xᵀ X` is invertible almost surely, exact `t` coverage and exact `F` size hold
  unconditionally.

The general tools are `ProbabilityTheory.ae_condDistrib_eq_map_of_indepFun` (conditional law of
`g X ε` given `X` for independent `X`, `ε`) and
`ProbabilityTheory.measure_preimage_inter_eq_of_indepFun` (its integrated form on an event of `X`).

Not covered: random designs whose errors are not conditionally Gaussian, heteroscedastic or
design-dependent error variances, rank-deficient designs (generalized inverses, `n - rank X`
with `rank X < p`), and laws of `X` under which `P(X full rank) = 1` is derived rather than
assumed.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-! ### The full-rank event and the residual degrees of freedom -/

omit [Fintype k] in
/-- A square real matrix of full rank is invertible. -/
private theorem isUnit_of_rank_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (h : S.rank = Fintype.card n) : IsUnit S := by
  rw [← mulVec_surjective_iff_isUnit]
  have hr : LinearMap.range S.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fintype_fun_eq_card]; exact h)
  exact LinearMap.range_eq_top.mp hr

/-- The full-rank designs: `X : Matrix m k ℝ` with invertible Gram matrix `Xᵀ X`, i.e. of full
column rank `card k` (`mem_fullRankDesigns_iff_rank`). -/
def fullRankDesigns (m k : Type*) [Fintype m] [Fintype k] [DecidableEq k] :
    Set (Matrix m k ℝ) :=
  {X | IsUnit (Xᵀ * X)}

omit [DecidableEq m] in
/-- A design is in `fullRankDesigns` iff it has rank `p = card k`. -/
theorem mem_fullRankDesigns_iff_rank (X : Matrix m k ℝ) :
    X ∈ fullRankDesigns m k ↔ X.rank = Fintype.card k := by
  rw [fullRankDesigns, Set.mem_ofPred_eq, ← rank_transpose_mul_self]
  exact ⟨rank_of_isUnit _, isUnit_of_rank_eq_card⟩

omit [DecidableEq m] in
/-- The full-rank event is measurable: it is the preimage of `{0}ᶜ` under `X ↦ det (Xᵀ X)`. -/
theorem measurableSet_fullRankDesigns : MeasurableSet (fullRankDesigns m k) := by
  have h : fullRankDesigns m k = (fun X : Matrix m k ℝ => (Xᵀ * X).det) ⁻¹' {0}ᶜ := by
    ext X
    simp [fullRankDesigns, Matrix.isUnit_iff_isUnit_det]
  rw [h]
  exact (continuous_id.matrix_transpose.matrix_mul continuous_id).matrix_det.measurable
    (measurableSet_singleton 0).compl

omit [DecidableEq m] in
/-- A full-rank design has at most as many columns as rows: `p ≤ n`. -/
theorem card_le_card_of_mem_fullRankDesigns {X : Matrix m k ℝ} (hX : X ∈ fullRankDesigns m k) :
    Fintype.card k ≤ Fintype.card m := by
  rw [← (mem_fullRankDesigns_iff_rank X).1 hX]
  exact rank_le_card_height X

/-- **Residual degrees of freedom on the full-rank event**: the residual-maker matrix of a
full-rank design has rank `n - rank X = n - p`. -/
theorem rank_residualMatrix_eq_card_sub_rank {X : Matrix m k ℝ}
    (hX : X ∈ fullRankDesigns m k) :
    (residualMatrix X).rank = Fintype.card m - X.rank := by
  rw [rank_residualMatrix hX, (mem_fullRankDesigns_iff_rank X).1 hX]

omit [DecidableEq m] in
/-- For a full-rank design and a hypothesis matrix `C` of full row rank, `C (Xᵀ X)⁻¹ Cᵀ` is
invertible: it is `(C B) (C B)ᵀ` with `B` the OLS matrix, and `rank (C B) = rank C`. -/
theorem isUnit_hypothesisGram {r : Type*} [Fintype r] [DecidableEq r] {X : Matrix m k ℝ}
    (hX : X ∈ fullRankDesigns m k) {C : Matrix r k ℝ} (hC : C.rank = Fintype.card r) :
    IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ) := by
  classical
  refine isUnit_of_rank_eq_card ?_
  have hG : C * (Xᵀ * X)⁻¹ * Cᵀ = (C * olsMatrix X) * (C * olsMatrix X)ᵀ := by
    rw [transpose_mul, ← olsMatrix_mul_transpose hX]
    simp only [Matrix.mul_assoc]
  rw [hG, rank_self_mul_transpose]
  refine le_antisymm (hC ▸ rank_mul_le_left _ _) ?_
  calc Fintype.card r = (C * olsMatrix X * X).rank := by
        rw [Matrix.mul_assoc, olsMatrix_mul_self hX, Matrix.mul_one, hC]
    _ ≤ (C * olsMatrix X).rank := rank_mul_le_left _ _

/-! ### Measurability of the statistics as functions of `(X, y)` -/

/-- Real matrix inversion is measurable (it is `det⁻¹ • adjugate`). -/
private theorem measurable_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun A : Matrix n n ℝ => A⁻¹) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact continuous_id.matrix_det.measurable.inv.mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

/-- Real matrices form a second-countable space, so products of matrix spaces carry their Borel
structure (needed to turn continuity into measurability on products). -/
local instance {n p : Type*} [Finite n] [Finite p] : SecondCountableTopology (Matrix n p ℝ) :=
  inferInstanceAs (SecondCountableTopology (n → p → ℝ))

omit [DecidableEq m] in
/-- Composition of a measurable function of `((Xᵀ X)⁻¹, X, y)` with the model map
`(X, e) ↦ ((Xᵀ X)⁻¹, X, X β + e)`. -/
private theorem measurable_gram_model {γ : Type*} [MeasurableSpace γ] (β : k → ℝ)
    {Φ : Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ)) → γ} (hΦ : Measurable Φ) :
    Measurable (fun p : Matrix m k ℝ × (m → ℝ) => Φ ((p.1ᵀ * p.1)⁻¹, (p.1, p.1 *ᵥ β + p.2))) :=
  hΦ.comp ((measurable_matrix_inv.comp
    (by fun_prop : Continuous fun p : Matrix m k ℝ × (m → ℝ) => p.1ᵀ * p.1).measurable).prodMk
    (by fun_prop : Continuous fun p : Matrix m k ℝ × (m → ℝ) => (p.1, p.1 *ᵥ β + p.2)).measurable)

private theorem measurable_olsEstimator_model (β : k → ℝ) :
    Measurable (Function.uncurry fun (x : Matrix m k ℝ) (e : m → ℝ) =>
      WithLp.toLp 2 (olsEstimator x (x *ᵥ β + e))) := by
  have hΦ : Measurable (fun q : Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ)) =>
      WithLp.toLp 2 ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) := by
    apply Continuous.measurable; fun_prop
  convert measurable_gram_model β hΦ using 1
  funext p
  simp only [Function.uncurry, olsEstimator, olsMatrix_eq]

private theorem measurable_rss_div_sq_model (β : k → ℝ) (σ : ℝ) :
    Measurable (Function.uncurry fun (x : Matrix m k ℝ) (e : m → ℝ) =>
      (x *ᵥ β + e - x *ᵥ olsEstimator x (x *ᵥ β + e)) ⬝ᵥ
        (x *ᵥ β + e - x *ᵥ olsEstimator x (x *ᵥ β + e)) / σ ^ 2) := by
  have hΦ : Measurable (fun q : Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ)) =>
      (q.2.2 - q.2.1 *ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) ⬝ᵥ
        (q.2.2 - q.2.1 *ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) / σ ^ 2) := by
    apply Continuous.measurable; fun_prop
  convert measurable_gram_model β hΦ using 1
  funext p
  simp only [Function.uncurry, olsEstimator, olsMatrix_eq]

private theorem measurable_tStatistic_model (a β : k → ℝ) :
    Measurable (Function.uncurry fun (x : Matrix m k ℝ) (e : m → ℝ) =>
      tStatistic x a β (x *ᵥ β + e)) := by
  have hΦ : Measurable (fun q : Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ)) =>
      a ⬝ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2 - β) /
        √((q.2.2 - q.2.1 *ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) ⬝ᵥ
          (q.2.2 - q.2.1 *ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) /
            ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * (a ⬝ᵥ (q.1 *ᵥ a)))) := by
    apply Measurable.div <;> apply Continuous.measurable <;> fun_prop
  convert measurable_gram_model β hΦ using 1
  funext p
  simp only [Function.uncurry, tStatistic, olsEstimator, olsMatrix_eq, contrastVariance]

private theorem measurable_fStatistic_model {r : Type*} [Fintype r] [DecidableEq r]
    (C : Matrix r k ℝ) (c : r → ℝ) (β : k → ℝ) :
    Measurable (Function.uncurry fun (x : Matrix m k ℝ) (e : m → ℝ) =>
      fStatistic x C c (x *ᵥ β + e)) := by
  have hCG : Continuous (fun q : Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ)) => C * q.1 * Cᵀ) := by
    fun_prop
  have hH := measurable_matrix_inv.comp hCG.measurable
  have hc : Continuous (fun z : Matrix r r ℝ × (Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ))) =>
      (C *ᵥ ((z.2.1 * z.2.2.1ᵀ) *ᵥ z.2.2.2) - c) ⬝ᵥ
        (z.1 *ᵥ (C *ᵥ ((z.2.1 * z.2.2.1ᵀ) *ᵥ z.2.2.2) - c))) := by
    fun_prop
  have hrss : Continuous (fun q : Matrix k k ℝ × (Matrix m k ℝ × (m → ℝ)) =>
      (q.2.2 - q.2.1 *ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) ⬝ᵥ
          (q.2.2 - q.2.1 *ᵥ ((q.1 * q.2.1ᵀ) *ᵥ q.2.2)) /
        ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) := by
    fun_prop
  have hΦ := ((hc.measurable.comp (hH.prodMk measurable_id)).div_const
    (Fintype.card r : ℝ)).div hrss.measurable
  convert measurable_gram_model β hΦ using 1
  funext p
  simp only [Function.uncurry, Function.comp, id, Pi.div_apply, fStatistic, olsEstimator,
    olsMatrix_eq]


end MathlibExt.Probability.Statistics.LinearModel

/-! ### Conditional laws of a function of an independent pair -/

namespace ProbabilityTheory

open MeasureTheory

variable {Ω D E γ : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace E]
  [MeasurableSpace γ] {μ : Measure Ω}

/-- The kernel `x ↦ ρ.map (g x)`: the law of `g x e` for `e ~ ρ` at a fixed first argument. -/
private noncomputable def sectionKernel (ρ : Measure E) (g : D → E → γ) : Kernel D γ :=
  (Kernel.id ×ₖ Kernel.const D ρ).map (Function.uncurry g)

private instance (ρ : Measure E) [IsFiniteMeasure ρ] (g : D → E → γ) :
    IsFiniteKernel (sectionKernel ρ g) := by
  unfold sectionKernel
  infer_instance

private theorem sectionKernel_apply (ρ : Measure E) [IsFiniteMeasure ρ] {g : D → E → γ}
    (hg : Measurable (Function.uncurry g)) (x : D) :
    sectionKernel ρ g x = ρ.map (g x) := by
  rw [sectionKernel, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
  rfl

/-- For independent `X` and `ε`, the joint law of `(X, g X ε)` disintegrates over `X` with
kernel `x ↦ (law ε).map (g x)`. -/
private theorem map_pair_eq_compProd [IsProbabilityMeasure μ] {X : Ω → D} {ε : Ω → E}
    (hX : AEMeasurable X μ) (hε : AEMeasurable ε μ) (hind : IndepFun X ε μ) {g : D → E → γ}
    (hg : Measurable (Function.uncurry g)) :
    μ.map (fun ω => (X ω, g (X ω) (ε ω))) = μ.map X ⊗ₘ sectionKernel (μ.map ε) g := by
  have hpg : Measurable (fun p : D × E => (p.1, Function.uncurry g p)) :=
    measurable_fst.prodMk hg
  have hpair : μ.map (fun ω => (X ω, g (X ω) (ε ω))) =
      (μ.map (fun ω => (X ω, ε ω))).map (fun p : D × E => (p.1, Function.uncurry g p)) := by
    rw [AEMeasurable.map_map_of_aemeasurable hpg.aemeasurable (hX.prodMk hε)]
    rfl
  rw [hpair, (indepFun_iff_map_prod_eq_prod_map_map hX hε).1 hind]
  ext s hs
  rw [Measure.map_apply hpg hs, Measure.prod_apply (hpg hs), Measure.compProd_apply hs]
  refine lintegral_congr fun x => ?_
  rw [sectionKernel_apply _ hg, Measure.map_apply
    (show Measurable (g x) from hg.comp measurable_prodMk_left) (measurable_prodMk_left hs)]
  rfl

/-- **Conditional law of a function of an independent pair**: if `X` and `ε` are independent,
then conditionally on `X = x` the variable `g X ε` has law `(law ε).map (g x)`, for
`(law X)`-almost every `x`. -/
theorem ae_condDistrib_eq_map_of_indepFun [StandardBorelSpace γ] [Nonempty γ]
    [IsProbabilityMeasure μ] {X : Ω → D} {ε : Ω → E} (hX : AEMeasurable X μ)
    (hε : AEMeasurable ε μ) (hind : IndepFun X ε μ) {g : D → E → γ}
    (hg : Measurable (Function.uncurry g)) :
    ∀ᵐ x ∂μ.map X, condDistrib (fun ω => g (X ω) (ε ω)) X μ x = (μ.map ε).map (g x) := by
  have hgm : AEMeasurable (fun ω => g (X ω) (ε ω)) μ := hg.comp_aemeasurable (hX.prodMk hε)
  filter_upwards [condDistrib_ae_eq_of_measure_eq_compProd hX hgm
    (map_pair_eq_compProd hX hε hind hg)] with x hx
  rw [hx, sectionKernel_apply _ hg]

/-- **Integrated conditional law on an event of the conditioning variable**: if `X` and `ε` are
independent and `g x ε` has the same law `ν` for every `x ∈ F`, then
`P(X ∈ F, g X ε ∈ S) = P(X ∈ F) · ν(S)`. -/
theorem measure_preimage_inter_eq_of_indepFun [IsProbabilityMeasure μ] {X : Ω → D}
    {ε : Ω → E} (hX : AEMeasurable X μ) (hε : AEMeasurable ε μ) (hind : IndepFun X ε μ)
    {g : D → E → γ} (hg : Measurable (Function.uncurry g)) {F : Set D} (hF : MeasurableSet F)
    {ν : Measure γ} (hν : ∀ x ∈ F, (μ.map ε).map (g x) = ν) {S : Set γ} (hS : MeasurableSet S) :
    μ (X ⁻¹' F ∩ {ω | g (X ω) (ε ω) ∈ S}) = μ (X ⁻¹' F) * ν S := by
  have hgm : AEMeasurable (fun ω => g (X ω) (ε ω)) μ := hg.comp_aemeasurable (hX.prodMk hε)
  have h := congrArg (fun κ : Measure (D × γ) => κ (F ×ˢ S)) (map_pair_eq_compProd hX hε hind hg)
  rw [Measure.map_apply_of_aemeasurable (hX.prodMk hgm) (hF.prod hS), Set.mk_preimage_prod,
    Measure.compProd_apply_prod hF hS,
    setLIntegral_congr_fun hF (fun x hx => by rw [sectionKernel_apply _ hg, hν x hx]),
    lintegral_const, Measure.restrict_apply_univ, Measure.map_apply_of_aemeasurable hX hF] at h
  rw [mul_comm, ← h]
  rfl

/-- **Conditional Gaussian-error hypothesis, unpacked**: if the conditional law of `Z` given `X`
is a.e. the fixed law `ρ`, then `Z` is independent of `X` and has law `ρ`. -/
theorem indepFun_hasLaw_of_condDistrib_ae_eq_const [IsProbabilityMeasure μ]
    [StandardBorelSpace E] [Nonempty E] {X : Ω → D} {Z : Ω → E} (hX : AEMeasurable X μ)
    (hZ : AEMeasurable Z μ) {ρ : Measure E} [IsProbabilityMeasure ρ]
    (hcond : condDistrib Z X μ =ᵐ[μ.map X] Kernel.const D ρ) :
    IndepFun X Z μ ∧ HasLaw Z ρ μ := by
  have hjoint : μ.map (fun ω => (X ω, Z ω)) = (μ.map X).prod ρ := by
    rw [(condDistrib_ae_eq_iff_measure_eq_compProd hX hZ _).1 hcond, Measure.compProd_const]
  have hlaw : μ.map Z = ρ := by
    rw [← Measure.snd_map_prodMk₀ hX hZ, hjoint, Measure.snd_prod]
  exact ⟨(indepFun_iff_map_prod_eq_prod_map_map hX hZ).2 (by rw [hjoint, hlaw]), ⟨hZ, hlaw⟩⟩

/-- Converse of `indepFun_hasLaw_of_condDistrib_ae_eq_const`: a variable `Z` with law `ρ`
independent of `X` has conditional law `ρ` given `X`. -/
theorem condDistrib_ae_eq_const_of_indepFun [IsProbabilityMeasure μ] [StandardBorelSpace E]
    [Nonempty E] {X : Ω → D} {Z : Ω → E} (hX : AEMeasurable X μ) {ρ : Measure E}
    [IsProbabilityMeasure ρ] (hind : IndepFun X Z μ) (hZ : HasLaw Z ρ μ) :
    condDistrib Z X μ =ᵐ[μ.map X] Kernel.const D ρ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd hX hZ.aemeasurable ?_
  rw [Measure.compProd_const, ← hZ.map_eq,
    (indepFun_iff_map_prod_eq_prod_map_map hX hZ.aemeasurable).1 hind]

end ProbabilityTheory

/-! ### The Gaussian linear model with a random design, conditionally on the design -/

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Matrix m k ℝ} {ε : Ω → m → ℝ} {σ : ℝ}

omit [DecidableEq m] [Fintype k] [DecidableEq k] in
/-- The conditional Gaussian-error hypothesis makes the design independent of the errors and
gives the standardized errors, as a function on the error space, the standard Gaussian law. -/
private theorem indepFun_hasLaw_of_condGaussian (hXm : AEMeasurable X μ)
    (hεm : AEMeasurable ε μ) (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1)) :
    IndepFun X ε μ ∧
      HasLaw (fun e : m → ℝ => σ⁻¹ • e) (Measure.pi fun _ : m => gaussianReal 0 1) (μ.map ε) := by
  obtain ⟨hind, hlaw⟩ :=
    indepFun_hasLaw_of_condDistrib_ae_eq_const hXm (hεm.const_smul σ⁻¹) hcond
  refine ⟨?_, ⟨(measurable_const_smul σ⁻¹).aemeasurable, ?_⟩⟩
  · have he : (fun x : m → ℝ => σ • x) ∘ (σ⁻¹ • ε) = ε := by
      funext ω
      simp [smul_smul, mul_inv_cancel₀ hσ.ne']
    have h := hind.comp measurable_id (measurable_const_smul σ)
    rwa [Function.id_comp, he] at h
  · rw [AEMeasurable.map_map_of_aemeasurable (measurable_const_smul σ⁻¹).aemeasurable hεm]
    exact hlaw.map_eq

/-- **Conditional law of the OLS estimator**: in `y = X β + ε` with a random design `X` and
errors whose standardized form `σ⁻¹ ε` is, conditionally on `X`, i.i.d. standard normal, for
`(law X)`-a.e. full-rank `x` the conditional law of `β̂` given `X = x` is `N(β, σ² (xᵀ x)⁻¹)`. -/
theorem ae_condDistrib_olsEstimator (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ)
    (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1)) (β : k → ℝ) :
    ∀ᵐ x ∂μ.map X, x ∈ fullRankDesigns m k →
      condDistrib (fun ω => WithLp.toLp 2 (olsEstimator (X ω) (X ω *ᵥ β + ε ω))) X μ x =
        multivariateGaussian (WithLp.toLp 2 β) (σ ^ 2 • (xᵀ * x)⁻¹) := by
  obtain ⟨hind, hlaw⟩ := indepFun_hasLaw_of_condGaussian hXm hεm hσ hcond
  filter_upwards [ae_condDistrib_eq_map_of_indepFun hXm hεm hind
    (measurable_olsEstimator_model β)] with x hx hfull
  rw [hx]
  exact (hasLaw_olsEstimator hfull β hσ hlaw).map_eq

/-- **Conditional law of the residual sum of squares**: for `(law X)`-a.e. full-rank `x`, and
`p < n`, the conditional law of `‖y - X β̂‖² / σ²` given `X = x` is `χ²_{n-p}`; here
`n - p = n - rank x` is the residual degrees of freedom (`rank_residualMatrix_eq_card_sub_rank`). -/
theorem ae_condDistrib_rss_div_sq (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ)
    (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) :
    ∀ᵐ x ∂μ.map X, x ∈ fullRankDesigns m k →
      condDistrib (fun ω => (X ω *ᵥ β + ε ω - X ω *ᵥ olsEstimator (X ω) (X ω *ᵥ β + ε ω)) ⬝ᵥ
          (X ω *ᵥ β + ε ω - X ω *ᵥ olsEstimator (X ω) (X ω *ᵥ β + ε ω)) / σ ^ 2) X μ x =
        chiSquareMeasure (Fintype.card m - Fintype.card k) := by
  obtain ⟨hind, hlaw⟩ := indepFun_hasLaw_of_condGaussian hXm hεm hσ hcond
  filter_upwards [ae_condDistrib_eq_map_of_indepFun hXm hεm hind
    (measurable_rss_div_sq_model β σ)] with x hx hfull
  rw [hx]
  exact (hasLaw_rss_div_sq hfull hkm β σ hσ hlaw).map_eq

/-- **Conditional `t` law of a contrast**: for `(law X)`-a.e. full-rank `x`, `p < n` and a
nonzero contrast `a`, the conditional law of the `t` statistic given `X = x` is `t_{n-p}`. -/
theorem ae_condDistrib_tStatistic (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ)
    (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) {a : k → ℝ} (ha : a ≠ 0) :
    ∀ᵐ x ∂μ.map X, x ∈ fullRankDesigns m k →
      condDistrib (fun ω => tStatistic (X ω) a β (X ω *ᵥ β + ε ω)) X μ x =
        studentTMeasure (Fintype.card m - Fintype.card k) := by
  obtain ⟨hind, hlaw⟩ := indepFun_hasLaw_of_condGaussian hXm hεm hσ hcond
  filter_upwards [ae_condDistrib_eq_map_of_indepFun hXm hεm hind
    (measurable_tStatistic_model a β)] with x hx hfull
  rw [hx]
  exact (hasLaw_tStatistic hfull hkm β hσ hlaw ha).map_eq

/-- **Conditional exact `t` coverage**: for `(law X)`-a.e. full-rank `x`,
`P(|T| ≤ c | X = x) = t_{n-p}([-c, c])`. -/
theorem ae_condDistrib_abs_tStatistic_le (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ)
    (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂μ.map X, x ∈ fullRankDesigns m k →
      (condDistrib (fun ω => tStatistic (X ω) a β (X ω *ᵥ β + ε ω)) X μ x).real
          {t | |t| ≤ c} =
        (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) := by
  filter_upwards [ae_condDistrib_tStatistic hXm hεm hσ hcond hkm β ha] with x hx hfull
  rw [hx hfull]
  congr 1
  ext t
  simp [abs_le]

/-- **Conditional `F` law of a linear hypothesis**: for `(law X)`-a.e. full-rank `x`, `p < n`,
a hypothesis matrix `C` of full row rank `q = card r > 0`, and under `H₀ : C β = c`, the
conditional law of the `F` statistic given `X = x` is `F(q, n - p)`. -/
theorem ae_condDistrib_fStatistic {r : Type*} [Fintype r] [DecidableEq r]
    (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ) (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hkm : Fintype.card k < Fintype.card m) {C : Matrix r k ℝ} (hC : C.rank = Fintype.card r)
    (hr : 0 < Fintype.card r) (β : k → ℝ) {c : r → ℝ} (hβ : C *ᵥ β = c) :
    ∀ᵐ x ∂μ.map X, x ∈ fullRankDesigns m k →
      condDistrib (fun ω => fStatistic (X ω) C c (X ω *ᵥ β + ε ω)) X μ x =
        snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k) := by
  obtain ⟨hind, hlaw⟩ := indepFun_hasLaw_of_condGaussian hXm hεm hσ hcond
  filter_upwards [ae_condDistrib_eq_map_of_indepFun hXm hεm hind
    (measurable_fStatistic_model C c β)] with x hx hfull
  rw [hx]
  exact (hasLaw_fStatistic hfull (isUnit_hypothesisGram hfull hC) hr hkm β hβ hσ hlaw).map_eq


/-- On an almost-sure event `B`, `μ.real (B ∩ A) = μ.real A` and `μ.real B = 1`. -/
private theorem measureReal_inter_of_ae {B : Set Ω} (hB : ∀ᵐ ω ∂μ, ω ∈ B) (A : Set Ω) :
    μ.real (B ∩ A) = μ.real A ∧ μ.real B = 1 := by
  have hc : μ Bᶜ = 0 := ae_iff.1 hB
  refine ⟨?_, ?_⟩
  · rw [measureReal_def, measureReal_def, Set.inter_comm, measure_inter_conull hc]
  · rw [measureReal_def, ← Set.univ_inter B, measure_inter_conull hc, measure_univ,
      ENNReal.toReal_one]

/-- **`t` statistic on the full-rank event**: for every measurable `S`,
`P(X full rank, T ∈ S) = P(X full rank) · t_{n-p}(S)`. -/
theorem measureReal_tStatistic_mem_inter (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ)
    (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) {a : k → ℝ} (ha : a ≠ 0)
    {S : Set ℝ} (hS : MeasurableSet S) :
    μ.real (X ⁻¹' fullRankDesigns m k ∩ {ω | tStatistic (X ω) a β (X ω *ᵥ β + ε ω) ∈ S}) =
      μ.real (X ⁻¹' fullRankDesigns m k) *
        (studentTMeasure (Fintype.card m - Fintype.card k)).real S := by
  obtain ⟨hind, hlaw⟩ := indepFun_hasLaw_of_condGaussian hXm hεm hσ hcond
  rw [measureReal_def, measure_preimage_inter_eq_of_indepFun hXm hεm hind
    (measurable_tStatistic_model a β) measurableSet_fullRankDesigns
    (fun x hx => (hasLaw_tStatistic hx hkm β hσ hlaw ha).map_eq) hS, ENNReal.toReal_mul]
  rfl

/-- **Exact `t` coverage when the design is a.s. of full rank**: if `Xᵀ X` is invertible
almost surely, then `P(|T| ≤ c) = t_{n-p}([-c, c])` for every `c`, unconditionally. -/
theorem measureReal_abs_tStatistic_le_of_ae_fullRank (hXm : AEMeasurable X μ)
    (hεm : AEMeasurable ε μ) (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hfull : ∀ᵐ ω ∂μ, X ω ∈ fullRankDesigns m k)
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) :
    μ.real {ω | |tStatistic (X ω) a β (X ω *ᵥ β + ε ω)| ≤ c} =
      (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) := by
  have h := measureReal_tStatistic_mem_inter hXm hεm hσ hcond hkm β ha
    (measurableSet_Icc (a := -c) (b := c))
  obtain ⟨h1, h2⟩ := measureReal_inter_of_ae (B := X ⁻¹' fullRankDesigns m k) hfull
    {ω | tStatistic (X ω) a β (X ω *ᵥ β + ε ω) ∈ Set.Icc (-c) c}
  rw [h1, h2, one_mul] at h
  rw [← h]
  congr 1
  ext ω
  simp [abs_le]

/-- **`F` statistic on the full-rank event**: under `H₀ : C β = c`, for every measurable `S`,
`P(X full rank, F ∈ S) = P(X full rank) · F(q, n - p)(S)`. -/
theorem measureReal_fStatistic_mem_inter {r : Type*} [Fintype r] [DecidableEq r]
    (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ) (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hkm : Fintype.card k < Fintype.card m) {C : Matrix r k ℝ} (hC : C.rank = Fintype.card r)
    (hr : 0 < Fintype.card r) (β : k → ℝ) {c : r → ℝ} (hβ : C *ᵥ β = c)
    {S : Set ℝ} (hS : MeasurableSet S) :
    μ.real (X ⁻¹' fullRankDesigns m k ∩ {ω | fStatistic (X ω) C c (X ω *ᵥ β + ε ω) ∈ S}) =
      μ.real (X ⁻¹' fullRankDesigns m k) *
        (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real S := by
  obtain ⟨hind, hlaw⟩ := indepFun_hasLaw_of_condGaussian hXm hεm hσ hcond
  rw [measureReal_def, measure_preimage_inter_eq_of_indepFun hXm hεm hind
    (measurable_fStatistic_model C c β) measurableSet_fullRankDesigns
    (fun x hx => (hasLaw_fStatistic hx (isUnit_hypothesisGram hx hC) hr hkm β hβ hσ
      hlaw).map_eq) hS, ENNReal.toReal_mul]
  rfl

/-- **Exact `F` test size when the design is a.s. of full rank**: if `Xᵀ X` is invertible almost
surely, then under `H₀ : C β = c`, `P(F ∈ S) = F(q, n - p)(S)` for every measurable `S`,
unconditionally. -/
theorem measureReal_fStatistic_mem_of_ae_fullRank {r : Type*} [Fintype r] [DecidableEq r]
    (hXm : AEMeasurable X μ) (hεm : AEMeasurable ε μ) (hσ : 0 < σ)
    (hcond : condDistrib (fun ω => σ⁻¹ • ε ω) X μ =ᵐ[μ.map X]
      Kernel.const _ (Measure.pi fun _ : m => gaussianReal 0 1))
    (hfull : ∀ᵐ ω ∂μ, X ω ∈ fullRankDesigns m k)
    (hkm : Fintype.card k < Fintype.card m) {C : Matrix r k ℝ} (hC : C.rank = Fintype.card r)
    (hr : 0 < Fintype.card r) (β : k → ℝ) {c : r → ℝ} (hβ : C *ᵥ β = c)
    {S : Set ℝ} (hS : MeasurableSet S) :
    μ.real {ω | fStatistic (X ω) C c (X ω *ᵥ β + ε ω) ∈ S} =
      (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real S := by
  have h := measureReal_fStatistic_mem_inter hXm hεm hσ hcond hkm hC hr β hβ hS
  obtain ⟨h1, h2⟩ := measureReal_inter_of_ae (B := X ⁻¹' fullRankDesigns m k) hfull
    {ω | fStatistic (X ω) C c (X ω *ᵥ β + ε ω) ∈ S}
  rwa [h1, h2, one_mul] at h

end MathlibExt.Probability.Statistics.LinearModel
