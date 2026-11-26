/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Machine
import CSLibExt.Computability.Complexity.Host

/-! # The total scan and membership in the canonical NP class -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.VerifierMachine

open Turing Function MetaMathlibExt BitstringEncoding TM2Program TM2Embedding
open Cslib.Complexity.DensestKSubgraph.Internal VerifierSpec VerifierBudget Cslib.Complexity
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF
open Cslib.Complexity.SatVerifier (Sym)
open MetaMathlibExt.ComplexityTheory MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
open Computability (encodeNat)

/- The only occupied initial stacks are the raw input and the proposed mask. -/
def init (x w : List Bool) : (s : K) → List (Γ s)
  | .dec s => Decode.st x [] [] s
  | .cur .mask => w
  | _ => []

private theorem dec_ok' : Embeds decEmb decLabel Decode.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem init_ready {x w : List Bool} {n k m : ℕ} {es : List (ℕ × ℕ)}
    {P : Decode.K → List Bool} {S : (j : K) → List (Γ j)}
    (ha : Agree decEmb P S) (hf : Frame decEmb (init x w) S)
    (hn : P (.n .output) = encodeNat n)
    (ht : Agree Decode.restEmb (ListNatPairPair.st [] [] (bitEncode (es.map Prod.fst))
        (bitEncode (es.map Prod.snd)) (encodeNat k) (encodeNat m)) P) :
    Ready n k m ⟨[], [], 0⟩ es w [] [] S := by
  have hD (j : Decode.K) : S (.dec j) = P j := (ha j).trans (List.map_id _)
  have hN : S nPort = encodeNat n := (hD _).trans hn
  have hK : S kPort = encodeNat k := (hD _).trans ((ht (.pair .left)).trans (List.map_id _))
  have hM : S mPort = encodeNat m := (hD _).trans ((ht (.pair .right)).trans (List.map_id _))
  have hA : S (column false) = bitEncode (es.map Prod.fst) :=
    (hD _).trans ((ht (.items (.output false))).trans (List.map_id _))
  have hB : S (column true) = bitEncode (es.map Prod.snd) :=
    (hD _).trans ((ht (.items (.output true))).trans (List.map_id _))
  constructor
  · intro j
    cases j with
    | mask => exact (hf (.cur .mask) (by simp [decEmb])).trans (List.map_id _).symm
    | split b p =>
      cases b <;> cases p
      case false.input => exact hA.trans (List.map_id _).symm
      case true.input => exact hB.trans (List.map_id _).symm
      all_goals exact hf _ (by simp [decEmb, curEmb, cursorPort])
  · intro j
    cases j with
    | word p =>
      cases p
      case bound => exact hN.trans (List.map_id _).symm
      all_goals exact hf _ (by simp [decEmb, rowEmb, rowPort])
    | dict b p =>
      cases b <;> cases p with
      | lookup l => cases l <;> exact hf _ (by simp [decEmb, rowEmb, rowPort])
      | _ => exact hf _ (by simp [decEmb, rowEmb, rowPort])
    | count b => cases b <;> exact hf _ (by simp [decEmb, rowEmb, rowPort])
    | _ => exact hf _ (by simp [decEmb, rowEmb, rowPort])
  · intro j
    cases j with
    | word p =>
      cases p
      case n => exact hN.trans (List.map_id _).symm
      case k => exact hK.trans (List.map_id _).symm
      case m => exact hM.trans (List.map_id _).symm
      case binaryCount => exact hf _ (by simp [decEmb, finEmb, finishPort])
    | count b => cases b <;> exact hf _ (by simp [decEmb, finEmb, finishPort])
    | _ => exact hf _ (by simp [decEmb, finEmb, finishPort])

private theorem check_eq {x : List Bool} (w : List Bool) {n k m : ℕ} {es : List (ℕ × ℕ)}
    (h : bitDecode x = some (n, es, k, m)) :
    densestCheck x w = true ↔ Accept n k m ⟨[], [], 0⟩ es w := by
  have hwf : wellFormedCheck (n, es, k, m) = true ↔ WellFormed (n, es, k, m) := by
    simp [wellFormedCheck, WellFormed, List.all_eq_true, and_assoc, and_left_comm, and_comm]
  rw [accept_initial_iff]
  simp only [densestCheck, h, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hwf]
  tauto

private theorem total_bound (x w : List Bool) (edges : ℕ) (he : edges ≤ x.length) :
    (10 * x.length + 6) + (edges * row (2 * x.length + 1) + finish (2 * x.length + 1)) ≤
      30000 * (x.length + w.length + 1) ^ 3 := by
  let L := x.length + w.length + 1
  have hx : x.length + 1 ≤ L := by dsimp [L]; omega
  have hL : 0 < L := by omega
  have hpow : L ≤ L ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hL (show 1 ≤ 3 by decide)
  have hrow : row (2 * x.length + 1) ≤ 1000 * (2 * L) ^ 2 := by
    unfold row
    gcongr
    omega
  have hfinish : finish (2 * x.length + 1) ≤ 20000 * L := by
    unfold finish
    omega
  have hwalk : edges * row (2 * x.length + 1) ≤ 4000 * L ^ 3 := by
    calc
      _ ≤ L * (1000 * (2 * L) ^ 2) := Nat.mul_le_mul (by omega) hrow
      _ = _ := by ring
  change _ ≤ 30000 * L ^ 3
  omega

/- The verifier halts within a cubic raw-input bound for every pair of raw bitstrings. -/
theorem total_run (x w : List Bool) (v : Bool) :
    ∃ z T, RunLe prog (30000 * (x.length + w.length + 1) ^ 3)
      ⟨some (.dec (.split .read)), v, init x w⟩
      ⟨some (if densestCheck x w then .yes else .no), z, T⟩ := by
  obtain ⟨z₁, P, hr, hP⟩ := Decode.run x v
  obtain ⟨S, hr₁, ha, hf⟩ := runLe_embed decLabel dec_ok' hr (S' := init x w)
    (by intro j; exact (List.map_id _).symm)
  cases hd : bitDecode (α := DensestKSubgraphInstance) x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, decLabel] at hr₁
    have hc : densestCheck x w = false := by simp [densestCheck, hd]
    refine ⟨z₁, S, ?_⟩
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact hr₁.mono ((Nat.le_add_right _ _).trans (total_bound x w 0 (Nat.zero_le _)))
  | some i =>
    obtain ⟨n, es, k, m⟩ := i
    obtain ⟨hn, hp⟩ := hP (n, es, k, m) hd
    obtain ⟨hf₀, hlen⟩ := decoded_fits hd
    have hready := init_ready ha hf hn hp
    have hhist := history_empty (2 * x.length + 1) es (by omega)
    obtain ⟨z, T, hr₂⟩ := loop_run (2 * x.length + 1) n k m es w ⟨[], [], 0⟩ z₁ S
      hready hf₀ hhist
    simp only [hd, Option.isSome_some, ↓reduceIte, decLabel] at hr₁
    rw [← check_eq w hd] at hr₂
    refine ⟨z, T, ?_⟩
    cases hb : densestCheck x w <;>
      simpa [hb] using (hr₁.trans hr₂).mono (total_bound x w _ hlen)

/- The Host packages the actual finite machine in its canonical input/output conventions. -/
theorem isPolyTime_check : IsPolyTime (fun q : List Bool × List Bool => densestCheck q.1 q.2) := by
  let c : Host.Comp := {
    K := K
    Γ := Γ
    finΓ := fun j => by
      cases j with
      | dec | cur => infer_instance
      | row j =>
        cases j with
        | dict b j => cases j <;> infer_instance
        | _ => infer_instance
      | fin j =>
        cases j with
        | code j => cases j <;> infer_instance
        | _ => infer_instance
    L := Lab
    prog := prog
    ks := Finset.univ.toList
    ks_nodup := Finset.nodup_toList _
    mem_ks := by simp }
  refine Host.isPolyTime_verifier (c := c) (cX := .dec Decode.input) (cW := .cur .mask)
    (gX := id) (gW := id) (start := .dec (.split .read)) (yes := .yes) (no := .no)
    densestCheck (Polynomial.C 30000 * (Polynomial.X + 1) ^ 3) (by decide) (by decide) rfl rfl ?_
  intro x w
  let vacant : (j : K) → List (Γ j) := fun _ => []
  have hinit : update (update vacant (.dec Decode.input) (x.map id)) (.cur .mask) (w.map id) =
      init x w := by
    funext j
    cases j with
    | dec j =>
      cases j with
      | rest j =>
        cases j with
        | items j =>
          cases j with
          | pair p =>
            cases p with
            | pair p => cases p <;> rfl
            | _ => rfl
          | _ => simp [vacant, init, Decode.st, ListNatPairPair.st, ListNatPair.st]
        | pair j =>
          cases j with
          | pair j => cases j <;> simp [vacant, init, Decode.st, Decode.input,
              ListNatPairPair.st, NatPair.st]
          | _ => rfl
      | n j => cases j <;> rfl
      | scratch => rfl
    | cur j =>
      cases j with
      | mask => simp [init]
      | split => rfl
    | row | fin => rfl
  change ∃ z T, RunLe prog ((Polynomial.C (30000 : ℕ) * (Polynomial.X + 1) ^ 3).eval
      (x.length + w.length))
    ⟨some (.dec (.split .read)), false,
      update (update vacant (.dec Decode.input) (x.map id)) (.cur .mask) (w.map id)⟩
    ⟨some (if densestCheck x w then .yes else .no), z, T⟩
  rw [hinit]
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one] using total_run x w false

/- One bit per decoded edge is a linear-length certificate for the exact decision language. -/
theorem mem_NP : densestKSubgraphDec ∈ NP := by
  refine ⟨Polynomial.X, fun q => densestCheck q.1 q.2, isPolyTime_check, ?_⟩
  intro x
  simpa only [Polynomial.eval_X] using densestKSubgraphDec_iff_marks x

end Cslib.Complexity.DensestKSubgraph.Internal.VerifierMachine
