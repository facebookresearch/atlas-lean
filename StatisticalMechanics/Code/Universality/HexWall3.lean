/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Universality.HexConnClosed
import Code.Universality.HexBridgeFull
import Code.Universality.HexBridgeWeight
import Code.Universality.HexBridgeRecon
import Code.Universality.HexSurgerySeams

namespace StatMech.Universality

open HexWalk List Filter Topology
open scoped BigOperators Topology Real NNReal











def hexWall3_ReachesWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re













def hexWall3_mem (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ b : HexBridge, b.width = T ∧ b.content = ts
    ∧ hexWall3_ReachesWidth a h0 T ts ∧ (HexWalk.ofTurns a h0 ts).IsLegalSAW



theorem hexWall3_mem_reaches (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (h : hexWall3_mem a h0 T ts) :
    ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re := by
  obtain ⟨b, _, _, hreach, _⟩ := h
  exact hreach
















noncomputable def hexWall3_column (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (hsummable : Summable (fun w : {ts // hexWall3_mem a h0 T ts} =>
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices))
    (hle_one : (∑' w : {ts // hexWall3_mem a h0 T ts},
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices) ≤ 1) :
    HexColumn T χ :=
  hexColumnOfWidth a h0 T χ (hexWall3_mem a h0 T)
    (hexWall3_mem_reaches a h0 T) hsummable hle_one



theorem hexWall3_column_colSum (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (hsummable hle_one) (y : ℝ) :
    (hexWall3_column a h0 T χ hsummable hle_one).colSum y
      = ∑' w : {ts // hexWall3_mem a h0 T ts},
          y ^ (HexWalk.ofTurns a h0 w.1).numVertices :=
  hexColumnOfWidth_colSum a h0 T χ (hexWall3_mem a h0 T)
    (hexWall3_mem_reaches a h0 T) hsummable hle_one y

















theorem hexWall3_bridge_mem (a : ℂ) (h0 : ℤ) (b : HexBridge)
    (hReaches : hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
    hexWall3_mem a h0 b.width b.content :=
  ⟨b, rfl, rfl, hReaches, hSAW⟩



















theorem hexWall3_colDomination_uncond (a : ℂ) (h0 : ℤ) (b : HexBridge) (χ : ℝ)
    (hsummable hle_one) {x : ℝ}
    (hx0 : 0 ≤ x) (hχ : 0 < χ) (hxχ : x ≤ χ)
    (hReaches : hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
    x ^ (HexWalk.ofTurns a h0 b.content).numVertices
      ≤ (hexWall3_column a h0 b.width χ hsummable hle_one).colSum x :=
  hexClosed_colDomination a h0 b.width χ (hexWall3_mem a h0 b.width)
    (hexWall3_mem_reaches a h0 b.width) hsummable hle_one
    hx0 hχ hxχ b.content (hexWall3_bridge_mem a h0 b hReaches hSAW)













theorem hexWall3_halfStep_re (h : ℤ) :
    (HexWalk.halfStep h).re = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
  unfold HexWalk.halfStep hexUnit
  rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
  have h1 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have h2 : ((1 : ℂ) / 2).im = 0 := by norm_num
  rw [h1, h2]; ring






theorem hexWall3_reachesWidth_witness (a : ℂ) :
    hexWall3_ReachesWidth a 0 1 [(-1 : ℤ)] := by
  refine ⟨a + HexWalk.halfStep 0 + HexWalk.halfStep (0 + (-1)) + HexWalk.halfStep (0 + (-1)),
    ?_, ?_⟩
  · unfold HexWalk.ofTurns HexWalk.vertices
    rw [HexWalk.verticesAux_cons, HexWalk.verticesAux_nil]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    right; trivial
  · simp only [Complex.add_re, Nat.cast_one]
    rw [show (0 : ℤ) + (-1) = -1 by ring, hexWall3_halfStep_re, hexWall3_halfStep_re]
    have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
    have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by
      push_cast; ring
    rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
    have hs3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
      rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hs3]





theorem hexWall3_isLegalSAW_witness (a : ℂ) :
    (HexWalk.ofTurns a 0 [(-1 : ℤ)]).IsLegalSAW := by
  constructor
  · intro t ht
    simp only [HexWalk.ofTurns, List.mem_singleton] at ht
    right; exact ht
  · unfold HexWalk.IsSAW HexWalk.ofTurns HexWalk.vertices
    rw [HexWalk.verticesAux_cons, HexWalk.verticesAux_nil, List.nodup_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton]
    intro hcontra
    have hhs : HexWalk.halfStep (0 + (-1)) ≠ 0 := by
      unfold HexWalk.halfStep
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨by norm_num, hexUnit_ne_zero _⟩
    apply hhs
    have htwo : (2 : ℂ) * HexWalk.halfStep (0 + (-1)) = 0 := by linear_combination -hcontra
    rcases mul_eq_zero.mp htwo with h | h
    · exact absurd h (by norm_num)
    · exact h





def hexWall3_witnessBridge : HexBridge where
  width := 1
  width_pos := one_pos
  content := [(-1 : ℤ)]
  content_ne := by simp






theorem hexWall3_witness_mem (a : ℂ) :
    hexWall3_mem a 0 1 [(-1 : ℤ)] :=
  hexWall3_bridge_mem a 0 hexWall3_witnessBridge
    (hexWall3_reachesWidth_witness a) (hexWall3_isLegalSAW_witness a)


















theorem hexWall3_bridgeProd_le (bs : List HexBridge) (h : StrictDecreasingWidths bs)
    (υ : ℕ → ℝ) (wtBr : HexBridge → ℝ)
    (hdom : ∀ b ∈ bs, wtBr b ≤ υ b.width)
    (hwtnn : ∀ b ∈ bs, 0 ≤ wtBr b) :
    (bs.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset bs, υ T := by
  rw [← hbw_prod_eq_finsetProd bs h υ]
  exact List.prod_map_le_prod_map₀ wtBr (fun b => υ b.width) hwtnn hdom








theorem hexWall3_weightBound_factor (x g : ℝ) (hx : 0 < x)
    (lower upper : List HexBridge)
    (hlo : StrictDecreasingWidths lower) (hup : StrictDecreasingWidths upper)
    (υ : ℕ → ℝ) (wtBr : HexBridge → ℝ)
    (hdomLo : ∀ b ∈ lower, wtBr b ≤ υ b.width)
    (hdomUp : ∀ b ∈ upper, wtBr b ≤ υ b.width)
    (hwtnn : ∀ b, 0 ≤ wtBr b)
    (htwo : g * x ^ 2 = (lower.map wtBr).prod * (upper.map wtBr).prod) :
    g ≤ (x ^ 2)⁻¹ *
      ((∏ T ∈ hbw_widthFinset lower, υ T) * (∏ T ∈ hbw_widthFinset upper, υ T)) := by
  have hloProd : (lower.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset lower, υ T :=
    hexWall3_bridgeProd_le lower hlo υ wtBr hdomLo (fun b _ => hwtnn b)
  have hupProd : (upper.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset upper, υ T :=
    hexWall3_bridgeProd_le upper hup υ wtBr hdomUp (fun b _ => hwtnn b)
  have hloNN : (0 : ℝ) ≤ (lower.map wtBr).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hupNN : (0 : ℝ) ≤ (upper.map wtBr).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hg : g = (x ^ 2)⁻¹ * ((lower.map wtBr).prod * (upper.map wtBr).prod) := by
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    field_simp at htwo ⊢; linarith [htwo]
  rw [hg]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul hloProd hupProd hupNN (le_trans hloNN hloProd)































noncomputable def hexWall3_HWDataRecon (a : ℂ) (h0 : ℤ) (c : ℕ → ℝ) (x : ℝ) (N : ℕ)
    (hx : 0 < x) (hlt : x < hexChiE)
    (hsum : ∀ T, Summable (fun w : {ts // hexWall3_mem a h0 T ts} =>
      hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices))
    (hle_one : ∀ T, (∑' w : {ts // hexWall3_mem a h0 T ts},
      hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) ≤ 1)
    (Dn : Type) [Fintype Dn]
    (wtγ : Dn → ℝ) (wtγ_nn : ∀ d, 0 ≤ wtγ d)
    (partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n)
    (lower upper : Dn → List HexBridge)
    (hlo : ∀ d, StrictDecreasingWidths (lower d))
    (hup : ∀ d, StrictDecreasingWidths (upper d))
    (htwoEdge : ∀ d, wtγ d * x ^ 2
        = ((lower d).map (fun b => x ^ (HexWalk.ofTurns a h0 b.content).numVertices)).prod
          * ((upper d).map (fun b => x ^ (HexWalk.ofTurns a h0 b.content).numVertices)).prod)
    (hReachesLo : ∀ d, ∀ b ∈ lower d, hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAWLo : ∀ d, ∀ b ∈ lower d, (HexWalk.ofTurns a h0 b.content).IsLegalSAW)
    (hReachesUp : ∀ d, ∀ b ∈ upper d, hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAWUp : ∀ d, ∀ b ∈ upper d, (HexWalk.ofTurns a h0 b.content).IsLegalSAW)
    (decomp_inj : Function.Injective
      (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))) :
    HexHWDataRecon c
      (fun T => (hexWall3_column a h0 T hexChiE (hsum T) (hle_one T)).colSum x) x N :=
  let Col : ∀ T, HexColumn T hexChiE :=
    fun T => hexWall3_column a h0 T hexChiE (hsum T) (hle_one T)
  let υ : ℕ → ℝ := fun T => (Col T).colSum x
  have hυnn : ∀ T, 0 ≤ υ T := fun T => (Col T).colSum_nonneg (le_of_lt hx)
  have hυle : ∀ T, υ T ≤ (x / hexChiE) ^ T :=
    fun T => (Col T).colSum_le_pow (le_of_lt hx) hexChiE_pos (le_of_lt hlt)
  have hmul : Multipliable (fun T => 1 + υ T) :=
    hex_bridge_multipliable υ (hex_ups_summable υ x (le_of_lt hx) hlt hυnn hυle)
  hexHWDataClosed c υ x N hυnn hmul
    Dn wtγ wtγ_nn partial_eq
    (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))
    decomp_inj
    (fun d => hexWall3_weightBound_factor x (wtγ d) hx (lower d) (upper d) (hlo d) (hup d)
      υ (fun b => x ^ (HexWalk.ofTurns a h0 b.content).numVertices)
      (fun b hb =>
        hexWall3_colDomination_uncond a h0 b hexChiE (hsum b.width) (hle_one b.width)
          (le_of_lt hx) hexChiE_pos (le_of_lt hlt) (hReachesLo d b hb) (hSAWLo d b hb))
      (fun b hb =>
        hexWall3_colDomination_uncond a h0 b hexChiE (hsum b.width) (hle_one b.width)
          (le_of_lt hx) hexChiE_pos (le_of_lt hlt) (hReachesUp d b hb) (hSAWUp d b hb))
      (fun b => by positivity)
      (htwoEdge d))

































theorem hex_connective_constant_2walls
    (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    (a : ℕ → ℂ) (h0 : ℕ → ℤ)
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    
    (hlamMono : ∀ v, 1 ≤ v → hexConnFinalLam B v ≤ hexConnFinalLam B (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < hexConnFinalUps B v)
    (hυnn : ∀ v, 0 ≤ hexConnFinalUps B v)
    (hτnn : ∀ v, 0 ≤ hexConnFinalTau B v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) =
      hexConnFinalLam B (v + 1) - hexConnFinalLam B v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hexConnFinalUps B (v + 1))
    
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < hexConnFinalTau B v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = hexConnFinalUps B)
    
    (aB : ℂ) (h0B : ℤ)
    (hColsum : ∀ T, Summable (fun w : {ts // hexWall3_mem aB h0B T ts} =>
      hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices))
    (hColle : ∀ T, (∑' w : {ts // hexWall3_mem aB h0B T ts},
      hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices) ≤ 1)
    
    (Dn : ∀ x, 0 < x → x < hexChiE → ∀ N, Type)
    (Dn_fin : ∀ x hx hxlt N, Fintype (Dn x hx hxlt N))
    (wtγ : ∀ x hx hxlt N, Dn x hx hxlt N → ℝ)
    (wtγ_nn : ∀ x hx hxlt N, ∀ d, 0 ≤ wtγ x hx hxlt N d)
    (partial_eq : ∀ x hx hxlt N,
      (Finset.univ (α := Dn x hx hxlt N)).sum (wtγ x hx hxlt N)
        = ∑ n ∈ Finset.range N, c n * x ^ n)
    (lower upper : ∀ x hx hxlt N, Dn x hx hxlt N → List HexBridge)
    (hlo : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (lower x hx hxlt N d))
    (hup : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (upper x hx hxlt N d))
    (htwoEdge : ∀ x hx hxlt N, ∀ d, wtγ x hx hxlt N d * x ^ 2
        = ((lower x hx hxlt N d).map
              (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod
          * ((upper x hx hxlt N d).map
              (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod)
    (decomp_inj : ∀ x hx hxlt N, Function.Injective
      (fun d => (hbw_widthFinset (lower x hx hxlt N d),
                 hbw_widthFinset (upper x hx hxlt N d))))
    
    (hReachesLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d,
      hexWall3_ReachesWidth aB h0B b.width b.content)
    (hSAWLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d,
      (HexWalk.ofTurns aB h0B b.content).IsLegalSAW)
    (hReachesUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d,
      hexWall3_ReachesWidth aB h0B b.width b.content)
    (hSAWUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d,
      (HexWalk.ofTurns aB h0B b.content).IsLegalSAW) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant_final c hge hsub a h0 B hFa hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc
    (fun T => hexWall3_column aB h0B T hexChiE (hColsum T) (hColle T))
    (fun x hx hxlt N =>
      letI := Dn_fin x hx hxlt N
      hexWall3_HWDataRecon aB h0B c x N hx hxlt (hColsum) (hColle)
        (Dn x hx hxlt N) (wtγ x hx hxlt N) (wtγ_nn x hx hxlt N) (partial_eq x hx hxlt N)
        (lower x hx hxlt N) (upper x hx hxlt N) (hlo x hx hxlt N) (hup x hx hxlt N)
        (htwoEdge x hx hxlt N)
        (hReachesLo x hx hxlt N) (hSAWLo x hx hxlt N)
        (hReachesUp x hx hxlt N) (hSAWUp x hx hxlt N)
        (decomp_inj x hx hxlt N))

end StatMech.Universality
