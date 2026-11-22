/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify
public import MathlibExt.Computability.TuringMachine.StackEmbedding

/-!
# Reusing the SUBSET-SUM verifier as a binary summing component

The existing verifier computes a mask-selected sum. Comparing it with an
empty target leaves the sum untouched: a nonempty sum mismatches at once.
The mapped terminal labels can be equal without being fresh or separate
from mapped live labels. `sum_embed` only reaches that common label;
callers establish its role in their host. Live source statements still
run through the unchanged `StackEmbedding` translation.

The explicit quadratic step bound is in framed input length. This helper
serves the PARTITION and KNAPSACK numeric reductions and verifiers.

Inputs must be canonical delimited `encodeNat` blocks. Normalize every
successfully decoded raw payload before using this driver. On malformed
or false-ending blocks the original verifier may reject early; merging
its halt labels would then continue with a partial sum, not a valid sum.
The stated theorems exclude that case through their exact input shape.
The mask stack is consumed. A caller computing multiple sums must copy
the original mask to each component before starting either run.
-/

@[expose] public section

namespace Cslib.Complexity.SSVerifierSum

open Cslib.Complexity.Karp Cslib.Complexity.SatVerifier
open MetaMathlibExt MetaMathlibExt.TM2Program Turing

private theorem compare_zero_run (w : List Sym) (bits : List Bool)
    (v : Bool) :
    ∃ v', Run SSVerify.prog 1
      ⟨some .cmp, v, SSVerify.st [] w [] [] (bits.map .bit)⟩
      ⟨some (if bits = [] then .yes else .no), v',
        SSVerify.st [] w [] [] (bits.map .bit)⟩ := by
  cases bits with
  | nil =>
    exact ⟨Flag.tag false, Run.single (by
      simp [SSVerify.prog, cmpB, TM2.stepAux, isBit, SSVerify.st])⟩
  | cons b bits =>
    refine ⟨Flag.tag false, Run.single ?_⟩
    cases b <;>
      simp [SSVerify.prog, cmpB, TM2.stepAux, isBit, bitOf,
        SSVerify.st, Sym.bit?]

/-- On canonical delimited `encodeNat` blocks, the existing component
leaves the selected sum at a halt label. Normalize raw payloads first:
malformed blocks can instead reject early, leaving only a partial sum.
The cost uses framed bit length, never numeric magnitudes. The mask is
consumed; copy it before reuse in another component. -/
theorem sum_component_run (as : List ℕ) (w : List Bool) (v : Bool) :
    let r := as.flatMap fun a =>
      BitstringEncoding.delimit (Computability.encodeNat a)
    let bits := Computability.encodeNat (SSVerify.pick as w).sum
    ∃ v' w', RunLe SSVerify.prog
      (r.length * (2 * r.length + 6) + r.length + 3)
      ⟨some .next, v, SSVerify.st (r.map .bit) (w.map .bit) [] [] []⟩
      ⟨some (if bits = [] then .yes else .no), v',
        SSVerify.st [] w' [] [] (bits.map .bit).reverse⟩ := by
  intro r bits
  have hd : SSVerify.numsAux r.length r = some as :=
    (SSVerify.numsAux_eq_some _ _ as le_rfl).mpr rfl
  obtain ⟨v₁, S₁, h₁, hS⟩ := SSVerify.loop_run r.length []
    r.length r w 0 v le_rfl (by simp [Computability.encodeNat,
      Computability.encodeNum])
  obtain ⟨hlen, w', he⟩ := hS as hd
  simp only [hd, Option.isSome_some, ↓reduceIte] at h₁
  rw [he] at h₁
  simp only [Nat.zero_add] at h₁ hlen
  obtain ⟨v₂, h₂⟩ := SSVerify.fmove_run [] w' [] bits v₁
  obtain ⟨v₃, h₃⟩ := compare_zero_run w' bits.reverse v₂
  simp only [List.map_reverse, List.reverse_eq_nil_iff] at h₃
  refine ⟨v₃, w', ((h₁.trans (h₂.le le_rfl)).trans
    (h₃.le le_rfl)).mono ?_⟩
  change bits.length ≤ r.length at hlen
  omega

/-- A mask long enough to select every item gives the original list. -/
theorem pick_all (as : List ℕ) (n : ℕ) (h : as.length ≤ n) :
    SSVerify.pick as (List.replicate n true) = as := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.replicate_succ, SSVerify.pick, List.headD_cons,
        ↓reduceIte, List.tail_cons]
      rw [ih n (by simpa using Nat.le_of_succ_le_succ h)]

open MetaMathlibExt.TM2Embedding in
/-- Reach the common mapped label after summing canonical `encodeNat`
blocks; unembedded stacks remain intact. The input agreement requires
prior normalization. A raw parse-failure exit can expose a partial sum.
This is only a reachability guarantee: `hφ` does not make the endpoint
fresh, distinct from mapped live labels, or a halt of the host. Callers
must establish their intended label separation and the code run next.
The embedded mask is consumed; each later sum needs its own saved copy. -/
theorem sum_embed {K Λ : Type} [DecidableEq K] {Γ : K → Type}
    (E : SEmb (fun _ : SSVerify.K => Sym) Γ)
    (φ : SSVerify.Lab → Λ) (M : Λ → TM2.Stmt Γ Λ Bool)
    (hM : Embeds E φ SSVerify.prog M) (hφ : φ .yes = φ .no)
    (as : List ℕ) (w : List Bool) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : Agree E (SSVerify.st
      ((as.flatMap fun a => BitstringEncoding.delimit
        (Computability.encodeNat a)).map .bit) (w.map .bit) [] [] []) S) :
    let n := (as.flatMap fun a => BitstringEncoding.delimit
      (Computability.encodeNat a)).length
    ∃ v' w' S', RunLe M (n * (2 * n + 6) + n + 3)
      ⟨some (φ .next), v, S⟩ ⟨some (φ .yes), v', S'⟩ ∧
      Agree E (SSVerify.st [] w' [] []
        ((Computability.encodeNat (SSVerify.pick as w).sum).map
          .bit).reverse) S' ∧ Frame E S S' := by
  intro n
  obtain ⟨v', w', hr⟩ := sum_component_run as w v
  obtain ⟨S', hrun, hagree, hframe⟩ := runLe_embed φ hM hr hS
  refine ⟨v', w', S', ?_, hagree, hframe⟩
  have he : φ (if Computability.encodeNat (SSVerify.pick as w).sum = []
      then .yes else .no) = φ .yes := by
    split <;> simp_all
  rwa [he] at hrun

end Cslib.Complexity.SSVerifierSum
