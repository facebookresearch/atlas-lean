/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Code.OSSS.Coding
import Code.OSSS.CovLowerBound
import Code.FK.FKG
import Code.FK.RussoDerivative

open scoped BigOperators
open Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS



namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]




noncomputable def fkMass (p q : ℝ) : ConfigSpace (Sym2 V) → ℝ := fun ω => FK.fkProb G p q ω



lemma fkMass_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    0 < fkMass G p q ω := FK.fkProb_pos G hp hp1 hq ω



lemma fkMass_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), fkMass G p q ω = 1 := FK.fkProb_sum_eq_one G hp hp1 hq























theorem fk_codeProb_eq_mass {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) (x : ConfigSpace (Sym2 V)) :
    (∏ t : Fin n, Coding.condProbBit (fkMass G p q)
        (Coding.prefixSet (σ : Fin n → Sym2 V) (t : ℕ)) x
        ((σ : Fin n → Sym2 V) t) (x ((σ : Fin n → Sym2 V) t)))
      = fkMass G p q x :=
  Coding.codeProb_eq_mass (fkMass G p q) (fkMass_pos G hp hp1 hq)
    (fkMass_sum_eq_one G hp hp1 hq) σ x











theorem fk_volume_codeFibre {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) (x : ConfigSpace (Sym2 V)) :
    (volume (Coding.codeFibre (fkMass G p q) σ x)).toReal = fkMass G p q x :=
  Coding.volume_codeFibre (fkMass G p q) (fkMass_pos G hp hp1 hq)
    (fkMass_sum_eq_one G hp hp1 hq) σ x













theorem fkMass_isMonotonic {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Monotonic.IsMonotonicMeasure (fkMass G p q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Monotonic.fkg_implies_monotonic
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq)

end MonotonicFK










namespace MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]




noncomputable def genMean (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, g ω * μ ω


noncomputable def genCov (μ : ConfigSpace E → ℝ) (f g : ConfigSpace E → ℝ) : ℝ :=
  genMean μ (fun ω => f ω * g ω) - genMean μ f * genMean μ g


noncomputable def genVar (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  genCov μ g g



noncomputable def genCoord (e : E) : ConfigSpace E → ℝ := fun ω => if ω e then (1 : ℝ) else 0

end MonotonicMeasure

namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open MonotonicMeasure


lemma genMean_fkMass (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    genMean (fkMass G p q) g = FK.fkMean G p q g := by
  unfold genMean fkMass FK.fkMean
  rfl


lemma genCov_fkMass (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    genCov (fkMass G p q) f g = FK.fkCov G p q f g := by
  unfold genCov FK.fkCov
  rw [genMean_fkMass, genMean_fkMass, genMean_fkMass]



lemma genCoord_eq_coord (e : Sym2 V) : (genCoord e : ConfigSpace (Sym2 V) → ℝ) = FK.coord e := by
  funext ω; unfold genCoord FK.coord; rfl



lemma genVar_fkMass_indicator (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ))) := by
  unfold genVar
  rw [genCov_fkMass]




lemma fkVar_indicator (p q : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) :
    genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) := by
  rw [genVar_fkMass_indicator]
  
  have hidem : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * A.indicator (fun _ => (1 : ℝ)) ω)
      = A.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  unfold FK.fkCov
  rw [hidem]
  
  show FK.fkMean G p q (A.indicator (fun _ => (1 : ℝ)))
      - FK.fkMean G p q (A.indicator (fun _ => (1 : ℝ)))
        * FK.fkMean G p q (A.indicator (fun _ => (1 : ℝ)))
    = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A)
  unfold FK.fkProbOf
  ring

end MonotonicFK



















namespace MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]











def MonotonicOSSSBound (μ : ConfigSpace E → ℝ) (s : Finset E)
    (f : ConfigSpace E → ℝ) (N : ℕ) (c₀ D : ℝ) : Prop :=
  (N : ℝ) * c₀ * genVar μ f ≤ D * ∑ e ∈ s, genCov μ (genCoord e) f

end MonotonicMeasure

namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open MonotonicMeasure


















theorem monotonicOSSS_to_fkCov (p : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) (N : ℕ) (c₀ D : ℝ)
    (hMonOSSS : MonotonicOSSSBound (fkMass G p 2) G.edgeFinset
      (A.indicator (fun _ => (1 : ℝ))) N c₀ D) :
    (N : ℝ) * c₀
        * (FK.fkProbOf G p 2 A * (1 - FK.fkProbOf G p 2 A))
      ≤ D * ∑ e ∈ G.edgeFinset,
          FK.fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  unfold MonotonicOSSSBound at hMonOSSS
  
  rw [fkVar_indicator G p 2 A] at hMonOSSS
  
  refine hMonOSSS.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  
  rw [genCov_fkMass, genCoord_eq_coord]
  unfold FK.fkCov
  rw [show (fun ω => FK.coord e ω * A.indicator (fun _ => (1 : ℝ)) ω)
        = (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * FK.coord e ω) from by funext ω; ring]
  ring

end MonotonicFK













namespace MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {ν : E → Bool → ℝ}

open StatMech.OSSS StatMech.OSSS.CovLowerBound



lemma genMean_weight (g : ConfigSpace E → ℝ) :
    genMean (weight ν) g = expect ν g := by
  unfold genMean expect
  exact Finset.sum_congr rfl (fun ω _ => by rw [mul_comm])


lemma genCov_weight (f g : ConfigSpace E → ℝ) :
    genCov (weight ν) f g = cov ν f g := by
  unfold genCov cov
  rw [genMean_weight, genMean_weight, genMean_weight]


lemma genVar_weight (g : ConfigSpace E → ℝ) :
    genVar (weight ν) g = var ν g := by
  unfold genVar var; rw [genCov_weight]



lemma genCoord_eq_coordI (e : E) : (genCoord e : ConfigSpace E → ℝ) = coordI e := by
  funext ω; unfold genCoord coordI; rfl








theorem monotonicOSSSBound_of_product {κ : Type*} [Fintype κ] [Nonempty κ]
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {f : ConfigSpace E → ℝ} (hf : f = A.indicator (fun _ => (1 : ℝ)))
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = f)
    (R : κ → E → ℝ) (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hD : ∀ e, (∑ k, R k e) ≤ D) :
    MonotonicOSSSBound (weight ν) Finset.univ f (Fintype.card κ) c₀ D := by
  unfold MonotonicOSSSBound
  rw [genVar_weight]
  have hmain := cov_lower_bound hν hA hf T hT R hR c₀ hc₀nn hc₀ D hDnn hD
  refine hmain.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [genCov_weight, genCoord_eq_coordI, cov_comm]

end MonotonicMeasure

end OSSS

end StatMech

