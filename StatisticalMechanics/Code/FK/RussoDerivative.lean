/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Code.FK.RandomCluster
import Code.Inequalities.Pivotal

open scoped BigOperators

namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]





noncomputable def openEdgeCount (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ e ∈ G.edgeFinset, (if ω e then (1 : ℝ) else 0)



noncomputable def fkMean (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), g ω * fkProb G p q ω



noncomputable def fkCov (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  fkMean G p q (fun ω => f ω * g ω) - fkMean G p q f * fkMean G p q g



noncomputable def coord (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  if ω e then (1 : ℝ) else 0








omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


lemma hasDerivAt_edgeFactor (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) (p : ℝ) :
    HasDerivAt (fun p => if ω e then p else 1 - p) (if ω e then (1 : ℝ) else -1) p := by
  by_cases h : ω e
  · simp only [h, if_true]; exact hasDerivAt_id p
  · simp only [h]
    simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)



noncomputable def edgeProductOff (p : ℝ) (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ j ∈ G.edgeFinset.erase e, (if ω j then p else 1 - p)



lemma hasDerivAt_edgeProduct (ω : ConfigSpace (Sym2 V)) (p : ℝ) :
    HasDerivAt (fun p => edgeProduct G p ω)
      (∑ e ∈ G.edgeFinset, edgeProductOff G p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  have h := HasDerivAt.finsetProd (u := G.edgeFinset)
    (f := fun (e : Sym2 V) (p : ℝ) => if ω e then p else 1 - p)
    (f' := fun (e : Sym2 V) => if ω e then (1 : ℝ) else -1)
    (x := p)
    (fun e _ => hasDerivAt_edgeFactor (V := V) ω e p)
  simp only [smul_eq_mul] at h
  have hfun : (fun p => edgeProduct G p ω)
      = (∏ i ∈ G.edgeFinset, fun (p : ℝ) => if ω i then p else 1 - p) := by
    funext q
    simp [edgeProduct, Finset.prod_apply]
  rw [hfun]
  refine h.congr_deriv ?_
  unfold edgeProductOff
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [mul_comm]



lemma edgeProduct_eq_off (p : ℝ) (e : Sym2 V) (ω : ConfigSpace (Sym2 V))
    (he : e ∈ G.edgeFinset) :
    edgeProduct G p ω = edgeProductOff G p e ω * (if ω e then p else 1 - p) := by
  unfold edgeProduct edgeProductOff
  rw [← Finset.prod_erase_mul G.edgeFinset _ he]




lemma edgeProductOff_term (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (e : Sym2 V)
    (ω : ConfigSpace (Sym2 V)) (he : e ∈ G.edgeFinset) :
    edgeProductOff G p e ω * (if ω e then (1 : ℝ) else -1)
      = edgeProduct G p ω * ((coord e ω - p) / (p * (1 - p))) := by
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  have hpne : p ≠ 0 := hp.ne'
  have hp1ne : (1 : ℝ) - p ≠ 0 := hp1'.ne'
  rw [edgeProduct_eq_off G p e ω he]
  unfold coord
  by_cases h : ω e = true
  · rw [if_pos h, if_pos h, if_pos h]
    field_simp
  · rw [if_neg h, if_neg h, if_neg h]
    field_simp
    ring

omit [DecidableEq V] in

lemma sum_coord_sub (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    ∑ e ∈ G.edgeFinset, (coord e ω - p)
      = openEdgeCount G ω - p * (G.edgeFinset.card : ℝ) := by
  rw [Finset.sum_sub_distrib]
  unfold openEdgeCount coord
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]



lemma hasDerivAt_edgeProduct_clean {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun p => edgeProduct G p ω)
      (edgeProduct G p ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
  refine (hasDerivAt_edgeProduct G ω p).congr_deriv ?_
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [edgeProductOff_term G p hp hp1 e ω he]




lemma hasDerivAt_fkWeight {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (q : ℝ)
    (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun p => fkWeight G p q ω)
      (fkWeight G p q ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
  have h := (hasDerivAt_edgeProduct_clean G hp hp1 ω).mul_const (q ^ numClusters G ω)
  refine h.congr_deriv ?_
  unfold fkWeight
  ring










noncomputable def fkNumer (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), g ω * fkWeight G p q ω


lemma fkNumer_one (p q : ℝ) : fkNumer G p q (fun _ => 1) = fkZ G p q := by
  unfold fkNumer fkZ
  exact Finset.sum_congr rfl (fun ω _ => by rw [one_mul])




lemma hasDerivAt_fkNumer {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (q : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun p => fkNumer G p q g)
      ((∑ ω : ConfigSpace (Sym2 V),
        g ω * (fkWeight G p q ω * (∑ e ∈ G.edgeFinset, (coord e ω - p))))
          / (p * (1 - p))) p := by
  unfold fkNumer
  have hsum : HasDerivAt (fun p => ∑ ω : ConfigSpace (Sym2 V), g ω * fkWeight G p q ω)
      (∑ ω : ConfigSpace (Sym2 V),
        g ω * (fkWeight G p q ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p))))) p := by
    apply HasDerivAt.fun_sum
    intro ω _
    exact (hasDerivAt_fkWeight G hp hp1 q ω).const_mul (g ω)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [mul_div_assoc, mul_div_assoc]




lemma fkMean_eq_div (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    fkMean G p q g = fkNumer G p q g / fkZ G p q := by
  unfold fkMean fkNumer fkProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [mul_div_assoc]


lemma fkMean_add (p q : ℝ) (g h : ConfigSpace (Sym2 V) → ℝ) :
    fkMean G p q (fun ω => g ω + h ω) = fkMean G p q g + fkMean G p q h := by
  unfold fkMean
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma fkMean_sum (p q : ℝ) {ι : Type*} (s : Finset ι)
    (g : ι → ConfigSpace (Sym2 V) → ℝ) :
    fkMean G p q (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, fkMean G p q (g i) := by
  unfold fkMean
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Finset.sum_mul]


lemma fkMean_const (p q : ℝ) {c : ℝ}
    (hZ : fkZ G p q ≠ 0) : fkMean G p q (fun _ => c) = c := by
  unfold fkMean fkProb
  have hstep : ∀ ω : ConfigSpace (Sym2 V), c * (fkWeight G p q ω / fkZ G p q)
      = (c * fkWeight G p q ω) / fkZ G p q := fun ω => by rw [mul_div_assoc]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), ← Finset.sum_div, ← Finset.mul_sum]
  show (c * fkZ G p q) / fkZ G p q = c
  rw [mul_div_assoc, div_self hZ, mul_one]


lemma fkMean_const_mul (p q : ℝ) (c : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    fkMean G p q (fun ω => c * g ω) = c * fkMean G p q g := by
  unfold fkMean
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  ring


lemma fkCov_add_right (p q : ℝ) (f g h : ConfigSpace (Sym2 V) → ℝ) :
    fkCov G p q f (fun ω => g ω + h ω)
      = fkCov G p q f g + fkCov G p q f h := by
  unfold fkCov
  have heq : (fun ω => f ω * (g ω + h ω)) = (fun ω => f ω * g ω + f ω * h ω) := by
    funext ω; ring
  rw [heq, fkMean_add, fkMean_add]
  ring


lemma fkCov_sum_right (p q : ℝ) {ι : Type*} (s : Finset ι)
    (f : ConfigSpace (Sym2 V) → ℝ) (g : ι → ConfigSpace (Sym2 V) → ℝ) :
    fkCov G p q f (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, fkCov G p q f (g i) := by
  unfold fkCov
  have hprod : fkMean G p q (fun ω => f ω * ∑ i ∈ s, g i ω)
      = ∑ i ∈ s, fkMean G p q (fun ω => f ω * g i ω) := by
    have heq : (fun ω => f ω * ∑ i ∈ s, g i ω)
        = (fun ω => ∑ i ∈ s, (fun i ω => f ω * g i ω) i ω) := by
      funext ω; rw [Finset.mul_sum]
    rw [heq, fkMean_sum G p q s (fun i ω => f ω * g i ω)]
  rw [hprod, fkMean_sum G p q s g, Finset.mul_sum, ← Finset.sum_sub_distrib]



lemma fkCov_sub_const (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) {c : ℝ}
    (hZ : fkZ G p q ≠ 0) :
    fkCov G p q f (fun ω => g ω - c) = fkCov G p q f g := by
  unfold fkCov
  have hprod : fkMean G p q (fun ω => f ω * (g ω - c))
      = fkMean G p q (fun ω => f ω * g ω) - c * fkMean G p q f := by
    have heq : (fun ω => f ω * (g ω - c)) = (fun ω => f ω * g ω + (-c) * f ω) := by
      funext ω; ring
    rw [heq, fkMean_add, fkMean_const_mul]
    ring
  have hgc : fkMean G p q (fun ω => g ω - c) = fkMean G p q g - c := by
    have heq : (fun ω => g ω - c) = (fun ω => g ω + (fun _ => -c) ω) := by funext ω; ring
    rw [heq, fkMean_add, fkMean_const G p q hZ]; ring
  rw [hprod, hgc]; ring









lemma fkCov_centeredCount (p q : ℝ) (hZ : fkZ G p q ≠ 0)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    fkCov G p q g (fun ω => ∑ e ∈ G.edgeFinset, (coord e ω - p))
      = ∑ e ∈ G.edgeFinset, fkCov G p q g (coord e) := by
  rw [fkCov_sum_right G p q G.edgeFinset g (fun e ω => coord e ω - p)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  exact fkCov_sub_const G p q g (coord e) hZ


















theorem hasDerivAt_fkMean {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun p => fkMean G p q g)
      ((∑ e ∈ G.edgeFinset, fkCov G p q g (coord e)) / (p * (1 - p))) p := by
  have hppos : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hpne : p * (1 - p) ≠ 0 := hppos.ne'
  have hZpos : 0 < fkZ G p q := fkZ_pos G hp hp1 hq
  have hZne : fkZ G p q ≠ 0 := hZpos.ne'
  
  set C : ConfigSpace (Sym2 V) → ℝ := fun ω => ∑ e ∈ G.edgeFinset, (coord e ω - p) with hC
  
  
  have hN : HasDerivAt (fun p => fkNumer G p q g)
      (fkNumer G p q (fun ω => g ω * C ω) / (p * (1 - p))) p := by
    have h := hasDerivAt_fkNumer G hp hp1 q g
    refine h.congr_deriv ?_
    congr 1
    unfold fkNumer
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [hC]; ring
  have hZd : HasDerivAt (fun p => fkZ G p q)
      (fkNumer G p q C / (p * (1 - p))) p := by
    have h := hasDerivAt_fkNumer G hp hp1 q (fun _ => 1)
    have hfun : (fun p => fkNumer G p q (fun _ => 1)) = (fun p => fkZ G p q) := by
      funext p; exact fkNumer_one G p q
    rw [hfun] at h
    refine h.congr_deriv ?_
    congr 1
    unfold fkNumer
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [hC]; ring
  
  have hdiv := HasDerivAt.div hN hZd hZne
  have hexp : (fun p => fkMean G p q g) = (fun p => fkNumer G p q g) / (fun p => fkZ G p q) := by
    funext p; rw [fkMean_eq_div]; rfl
  rw [hexp]
  refine hdiv.congr_deriv ?_
  
  have hgC : fkMean G p q (fun ω => g ω * C ω) = fkNumer G p q (fun ω => g ω * C ω) / fkZ G p q :=
    fkMean_eq_div G p q _
  have hCexp : fkMean G p q C = fkNumer G p q C / fkZ G p q := fkMean_eq_div G p q _
  have hgexp : fkMean G p q g = fkNumer G p q g / fkZ G p q := fkMean_eq_div G p q g
  
  have hcov : fkCov G p q g C
      = (fkNumer G p q (fun ω => g ω * C ω) * fkZ G p q - fkNumer G p q g * fkNumer G p q C)
          / (fkZ G p q) ^ 2 := by
    unfold fkCov
    rw [hgC, hCexp, hgexp]
    field_simp
  
  rw [← fkCov_centeredCount G p q hZne g]
  show (fkNumer G p q (fun ω => g ω * C ω) / (p * (1 - p)) * fkZ G p q
        - fkNumer G p q g * (fkNumer G p q C / (p * (1 - p)))) / fkZ G p q ^ 2
      = fkCov G p q g C / (p * (1 - p))
  rw [hcov]
  field_simp




theorem deriv_fkMean {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    deriv (fun p => fkMean G p q g) p
      = (∑ e ∈ G.edgeFinset, fkCov G p q g (coord e)) / (p * (1 - p)) :=
  (hasDerivAt_fkMean G hp hp1 hq g).deriv











noncomputable def fkProbOf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  fkMean G p q (A.indicator (fun _ => (1 : ℝ)))







theorem hasDerivAt_fkProbOf {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    HasDerivAt (fun p => fkProbOf G p q A)
      ((∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e))
        / (p * (1 - p))) p :=
  hasDerivAt_fkMean G hp hp1 hq _


theorem deriv_fkProbOf {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    deriv (fun p => fkProbOf G p q A) p
      = (∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e))
        / (p * (1 - p)) :=
  (hasDerivAt_fkProbOf G hp hp1 hq A).deriv













noncomputable def russoPrefactor (p : ℝ) : ℝ := 1 / (p * (1 - p))


lemma russoPrefactor_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < russoPrefactor p :=
  one_div_pos.2 (mul_pos hp (by linarith))






theorem russo_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    russoPrefactor p * (∑ e ∈ G.edgeFinset,
        fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e))
      ≤ deriv (fun p => fkProbOf G p q A) p := by
  rw [deriv_fkProbOf G hp hp1 hq A]
  unfold russoPrefactor
  rw [one_div, div_eq_inv_mul]

end FK

end StatMech
