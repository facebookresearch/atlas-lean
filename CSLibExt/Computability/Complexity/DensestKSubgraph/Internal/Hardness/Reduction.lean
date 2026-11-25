/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Hardness.Prepare
public import CSLibExt.Computability.Complexity.Karp.CliqueComplete

/-! # Canonical polynomial-time CLIQUE-to-DENSEST k-SUBGRAPH reduction -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.CliqueReduction

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding
open MetaMathlibExt.BitstringEncoding MetaMathlibExt.ComplexityTheory
open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
open Cslib.Complexity.DensestKSubgraph.Internal.CliqueCorrect
open Computability (encodeNat)

/- The preparation, walk, and emission workspaces. -/
inductive K | prep (s : CliquePrepare.K) | walk (s : CliqueWalk.K) | code (s : EmitSS.K) | buffer
  deriving DecidableEq

instance : Fintype K where
  elems := {K.buffer} ∪ Finset.univ.image K.prep ∪ Finset.univ.image K.walk ∪
    Finset.univ.image K.code
  complete k := by cases k <;> simp

/- The finite alphabets are reused without changing their encodings. -/
@[reducible] def Γ : K → Type
  | .prep k => CliquePrepare.Γ k
  | .walk k => CliqueWalk.Γ k
  | .code k => EmitSS.Γ k
  | .buffer => Bool

/- The three numeric serialization sites, in right-to-left order. -/
inductive Phase | m | k | n
  deriving DecidableEq

instance : Fintype Phase := Fintype.ofList [.m, .k, .n] (by intro p; cases p <;> decide)

/- The fixed control phases. -/
inductive Lab
  | prep (l : CliquePrepare.Lab) | walk (l : CliqueWalk.Lab) | code (p : Phase) (l : UnaryNat.Lab)
  | edges | unreverse | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.edges, .unreverse, .done} ∪ Finset.univ.image Lab.prep ∪
    Finset.univ.image Lab.walk ∪ Finset.univ.image (fun p : Phase × UnaryNat.Lab => .code p.1 p.2)
  complete l := by cases l <;> simp

/- The validation stage occupies its copy of the preparation stacks. -/
def prepEmb : SEmb CliquePrepare.Γ Γ where
  e := K.prep
  inj _ _ h := K.prep.inj h
  ι _ := Equiv.refl _

/- The reverse adjacency tape and the vertex count feed the reverse walk directly. -/
def walkSlot : CliqueWalk.K → K
  | .r .bits => .prep .matrix
  | .r .i => .prep .n
  | k => .walk k

/- All other workspace is private to the walker. -/
def walkEmb : SEmb CliqueWalk.Γ Γ where
  e := walkSlot
  inj a b h := by
    rcases a with a | _ | _ <;> rcases b with b | _ | _ <;>
      (try cases a) <;> (try cases b) <;> cases h <;> rfl
  ι k := by
    cases k with
    | r k => cases k <;> exact Equiv.refl _
    | _ => exact Equiv.refl _

/- The walker's final `d` holds the original `n`. -/
def source : Phase → K
  | .m => .prep .threshold
  | .k => .prep .sizeK
  | .n => .walk .d

/- Consume a different physical counter at each serialization site. -/
def codeSlot (p : Phase) : EmitSS.K → K
  | .A => source p
  | k => .code k

/- All sites reuse the same bit output and restore the same work stacks. -/
def codeEmb (p : Phase) : SEmb EmitSS.Γ Γ where
  e := codeSlot p
  inj a b h := by cases p <;> cases a <;> cases b <;> cases h <;> rfl
  ι k := by cases k <;> cases p <;> exact Equiv.refl _

/- The raw threshold is the rightmost field and has no surrounding frame. -/
def framed : Phase → Bool
  | .m => false
  | _ => true

/- Encode the pair length and reject bad preparation before writing output. -/
def prepLabel : CliquePrepare.Lab → Lab
  | .good => .walk .head
  | .bad => .done
  | l => .prep l

/- Once the edges are available, emit the threshold first. -/
def walkLabel : CliqueWalk.Lab → Lab
  | .done => .code .m (.emit .hv)
  | l => .walk l

/- Termination and routing between serialization sites. -/
def codeLabel (p : Phase) : UnaryNat.Lab → Lab
  | .done => match p with
    | .m => .code .k (.emit .hv)
    | .k => .edges
    | .n => .done
  | l => .code p l

/- Canonical tuple serialization interleaved with the three finite components. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .prep l => mapS prepEmb prepLabel (CliquePrepare.prog l)
  | .walk l => mapS walkEmb walkLabel (CliqueWalk.prog l)
  | .code p l => mapS (codeEmb p) (codeLabel p) (UnaryNat.prog (framed p) l)
  | .edges => emitFrame (.walk (.r (.edge .output))) .buffer some id .edges .unreverse
  | .unreverse => moveB .buffer (.code .O) some id .unreverse (.code .n (.emit .hv))
  | .done => .halt

private theorem prep_ok : Embeds prepEmb prepLabel CliquePrepare.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem walk_ok : Embeds walkEmb walkLabel CliqueWalk.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem code_ok (p : Phase) : Embeds (codeEmb p) (codeLabel p)
    (UnaryNat.prog (framed p)) prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

/- Three reusable empty stacks at each numeric call. -/
def scratch (S : (k : K) → List (Γ k)) : Prop :=
  S (.code .X) = [] ∧ S (.code .H) = [] ∧ S (.code .T) = []

/- Raw or framed payload for the serialization site. -/
def payload (p : Phase) (n : ℕ) : List Bool :=
  if framed p then delimit (encodeNat n) else encodeNat n

private def localCode (p : Phase) (S : (k : K) → List (Γ k)) (j : EmitSS.K) :
    List (EmitSS.Γ j) := (S ((codeEmb p).e j)).map ((codeEmb p).ι j).symm

private theorem embed_num (p : Phase) (n : ℕ) (out : List Bool) (v : Bool)
    (S : (k : K) → List (Γ k)) (hn : localCode p S .A = cnt EmitSS.U n)
    (hs : scratch S) (ho : S (.code .O) = out) :
    ∃ w T, RunLe prog (710 * n + 306) ⟨some (.code p (.emit .hv)), v, S⟩
      ⟨some (codeLabel p .done), w, T⟩ ∧ T (.code .O) = payload p n ++ out ∧
      scratch T ∧ Frame (codeEmb p) S T := by
  have ha : Agree (codeEmb p) (localCode p S) S := by
    intro j
    simp [localCode, List.map_map, Function.comp_def]
  have hl (j : EmitSS.K) (hj : j ≠ .A) : localCode p S j = S (.code j) := by
    cases j <;> cases p <;> first | contradiction | exact List.map_id _
  have hh := (hl .H (by decide)).trans hs.2.1
  have ht := (hl .T (by decide)).trans hs.2.2
  have hx := (hl .X (by decide)).trans hs.1
  have hos := (hl .O (by decide)).trans ho
  have hraw : ∃ w U, RunLe (UnaryNat.prog (framed p)) (710 * n + 306)
      ⟨some (.emit .hv), v, localCode p S⟩ ⟨some .done, w, U⟩ ∧
      U .O = payload p n ++ out ∧ U .X = [] ∧ U .H = [] ∧ U .T = [] := by
    cases p with
    | m =>
      obtain ⟨w, U, hr, huo, -, huh, hut, hux, -⟩ :=
        UnaryNat.run_raw n out v _ (hn) hh ht hos hx
      exact ⟨w, U, hr, huo, hux, huh, hut⟩
    | k | n =>
      obtain ⟨U, hr, huo, -, huh, hut, hf⟩ := UnaryNat.run_framed n out v _ (hn) hh ht hos
      exact ⟨false, U, hr.mono (by omega), huo,
        (hf .X (by decide) (by decide) (by decide) (by decide)).trans hx, huh, hut⟩
  obtain ⟨w, U, hr, huo, hux, huh, hut⟩ := hraw
  obtain ⟨T, hrun, hac, hf⟩ := runLe_embed (codeLabel p) (code_ok p) hr ha
  have hout (j : EmitSS.K) (hj : j ≠ .A) : T (.code j) = U j := by
    have ha' := hac j
    cases j <;> cases p <;> first | contradiction | exact ha'.trans (List.map_id _)
  exact ⟨w, T, hrun, (hout .O (by decide)).trans huo,
    ⟨(hout .X (by decide)).trans hux, (hout .H (by decide)).trans huh,
      (hout .T (by decide)).trans hut⟩, hf⟩

private theorem localCode_m (S : (k : K) → List (Γ k)) :
    localCode .m S .A = S (.prep .threshold) := List.map_id _

private theorem localCode_k (S : (k : K) → List (Γ k)) :
    localCode .k S .A = S (.prep .sizeK) := List.map_id _

private theorem localCode_n (S : (k : K) → List (Γ k)) :
    localCode .n S .A = S (.walk .d) := List.map_id _

private theorem assemble_edges (es out : List Bool) (v : Bool) (S : (k : K) → List (Γ k))
    (he : S (.walk (.r (.edge .output))) = es) (ho : S (.code .O) = out)
    (hb : S .buffer = []) :
    ∃ w T, RunLe prog (3 * es.length + 3) ⟨some .edges, v, S⟩
      ⟨some (.code .n (.emit .hv)), w, T⟩ ∧ T (.code .O) = delimit es ++ out ∧
      ∀ j, j ≠ .walk (.r (.edge .output)) → j ≠ .buffer → j ≠ .code .O → T j = S j := by
  obtain ⟨U, h₁, -, hu, hf⟩ := emitFrame_run (M := prog) (self := .edges) (next := .unreverse)
    rfl (by decide) id (fun _ => rfl) es [] v S rfl (by simpa using he)
  have hu' : U .buffer = (delimit es).reverse := by simpa [hb] using hu
  obtain ⟨w, T, h₂, -, ht, hTf⟩ := moveB_run (M := prog) (self := .unreverse)
    (next := .code .n (.emit .hv)) rfl (by decide) (delimit es).reverse (delimit es).reverse []
    false U (by simpa using hu') rfl rfl
  refine ⟨w, T, (h₁.trans h₂).le ?_, ?_, fun j hj₁ hj₂ hj₃ => ?_⟩
  · rw [List.length_reverse, length_delimit]; omega
  · rw [ht, hf _ (by decide) (by decide), ho]
    simp
  · rw [hTf j hj₂ hj₃, hf j hj₁ hj₂]

private theorem walk_excludes {j : K} (hm : K.prep .matrix ≠ j) (hn : K.prep .n ≠ j)
    (hw : ∀ w, K.walk w ≠ j) (w : CliqueWalk.K) : walkSlot w ≠ j := by
  cases w with
  | r r => cases r <;> first | exact hm | exact hn | exact hw _
  | d | temp => exact hw _

private theorem mem_parse {x bits : List Bool} {k n : ℕ}
    (h : CliquePrepare.parse x = some (k, n, bits)) :
    decodeKG x = some (k, n, bits) ∧ bits.length = (pairs n).length := by
  unfold CliquePrepare.parse at h
  exact (Option.filter_eq_some_iff.mp h).imp_right (by simp)

private theorem encodeList_bound (n : ℕ) (es : List (ℕ × ℕ))
    (h : ∀ e ∈ es, e.1 ≤ n ∧ e.2 ≤ n) :
    (bitEncode es).length ≤ es.length * (6 * n + 3) := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    have he := h e (by simp)
    have he₁ := EmitSS.encodeNat_length_le e.1
    have he₂ := EmitSS.encodeNat_length_le e.2
    have h₁ : (bitEncode e.1).length ≤ n := he₁.trans he.1
    have h₂ : (bitEncode e.2).length ≤ n := he₂.trans he.2
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    change (delimit (bitEncode e) ++ bitEncode es).length ≤ _
    rw [List.length_cons, Nat.succ_mul, List.length_append, length_delimit]
    change 2 * (delimit (bitEncode e.1) ++ bitEncode e.2).length + 1 + _ ≤ _
    rw [List.length_append, length_delimit]
    omega

private theorem edgeLength_bound (n : ℕ) (bits : List Bool) :
    (bitEncode (edgesOfBits n bits)).length ≤ bits.length * (6 * n + 3) := by
  have hl : (edgesOfBits n bits).length ≤ bits.length := by
    unfold edgesOfBits markedEdges
    exact (List.length_filterMap_le _ _).trans (by simp)
  refine (encodeList_bound n _ ?_).trans (Nat.mul_le_mul_right _ hl)
  intro e he
  obtain ⟨⟨p, b⟩, h, hh⟩ := List.mem_filterMap.mp he
  cases b with
  | false => cases hh
  | true =>
    have hpe : p = e := Option.some.inj hh
    subst p
    obtain ⟨u, v⟩ := e
    obtain ⟨hu, hv⟩ := mem_pairs.mp (List.of_mem_zip h).1
    exact ⟨(hu.trans hv).le, hv.le⟩

/- All work starts with empty stacks other than the bit input. -/
def init (x : List Bool) : (k : K) → List (Γ k)
  | .prep p => CliquePrepare.init x p
  | _ => []

private theorem bounded_total (x : List Bool) (v : Bool) :
    ∃ w T, RunLe prog (6000 * (x.length + 1) ^ 3)
      ⟨some (.prep .rk), v, init x⟩ ⟨some .done, w, T⟩ ∧ T (.code .O) = cliqueToDensest x := by
  let L := x.length
  obtain ⟨w₁, P, rp, hp⟩ := CliquePrepare.run x v
  obtain ⟨S₁, r₁, a₁, f₁⟩ := runLe_embed prepLabel prep_ok rp (S' := init x) (by
    intro k; exact (List.map_id _).symm)
  cases h : CliquePrepare.parse x with
  | none =>
    have hOut : cliqueToDensest x = [] := by
      unfold CliquePrepare.parse at h
      unfold cliqueToDensest
      cases hc : decodeKG x with
      | none => rfl
      | some q =>
        obtain ⟨k, n, bits⟩ := q
        by_cases hh : bits.length = (pairs n).length
        · simp [hc, hh] at h
        · simp [hh]
    simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, prepLabel] at r₁
    have hpows : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hb := Nat.mul_le_mul (show 20 ≤ 6000 by decide) hpows
    refine ⟨w₁, S₁, r₁.mono hb, ?_⟩
    rw [f₁ _ (by intro j; simp [prepEmb]), hOut]
    rfl
  | some q =>
    obtain ⟨k, n, bits⟩ := q
    obtain ⟨hd, hbits⟩ := mem_parse h
    have hx := decodeKG_eq_some_iff.mp hd
    have hlen : L = k + n + bits.length + 2 := by
      dsimp [L]
      rw [hx]
      simp [encodeKG]
      omega
    have hk : k ≤ L := by omega
    have hn : n ≤ L := by omega
    have hm : k.choose 2 ≤ L ^ 2 := by
      rw [Nat.choose_two_right, pow_two]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hk (by omega))
    have ha (j : CliquePrepare.K) : S₁ (.prep j) = P j := (a₁ j).trans (List.map_id _)
    have hf (j : K) (hj : ∀ a, K.prep a ≠ j) : S₁ j = init x j := f₁ j hj
    obtain ⟨hk₁, hn₁, hm₁, hb₁⟩ := hp k n bits h
    simp only [h, Option.isSome_some, ↓reduceIte, prepLabel] at r₁
    have hrev : bits.reverse.length = (CliqueWalk.revPairsPrefix n n).length := by
      simpa [CliqueWalk.revPairs_eq] using hbits
    obtain ⟨w₂, rw₂⟩ := CliqueWalk.run n n le_rfl bits.reverse [] w₁ hrev
    have h0 : Agree walkEmb (CliqueWalk.st bits.reverse n 0 0 (n - n) []) S₁ := by
      intro slot
      cases slot with
      | r slot =>
        cases slot with
        | bits => exact ((ha _).trans hb₁).trans (List.map_id _).symm
        | i => exact ((ha _).trans hn₁).trans (List.map_id _).symm
        | j | left | temp => exact hf _ (by intro a; decide +revert)
        | edge l =>
          have hv := hf (.walk (.r (.edge l))) (by intro a; simp)
          cases l with
          | «local» l => cases l <;> exact hv
          | _ => exact hv
      | d => rw [Nat.sub_self]; exact hf _ (by intro a; decide +revert)
      | temp => exact hf _ (by intro a; decide +revert)
    obtain ⟨S₂, r₂, a₂, f₂⟩ := runLe_embed walkLabel walk_ok rw₂ h0
    let ed := bitEncode (edgesOfBits n bits)
    have hE : S₂ (.walk (.r (.edge .output))) = ed := by
      have he := (a₂ (.r (.edge .output))).trans (List.map_id _)
      change S₂ (.walk (.r (.edge .output))) = CliqueWalk.emitPrefix n n bits.reverse [] at he
      simpa [CliqueWalk.emitPrefix_eq n bits [] hbits, ed] using he
    have hN : S₂ (.walk .d) = cnt EmitSS.U n := (a₂ .d).trans (List.map_id _)
    have hW (j : K) (hj : ∀ a, walkSlot a ≠ j) : S₂ j = S₁ j := f₂ j hj
    have hM : S₂ (.prep .threshold) = cnt EmitSS.U (k.choose 2) := by
      rw [hW _ (walk_excludes (by decide) (by decide) (by simp)), ha, hm₁]
    have hK : S₂ (.prep .sizeK) = cnt EmitSS.U k := by
      rw [hW _ (walk_excludes (by decide) (by decide) (by simp)), ha, hk₁]
    have hbase (j : EmitSS.K) : S₂ (.code j) = [] := by
      rw [hW _ (walk_excludes (by simp) (by simp) (by simp)), hf]
      · rfl
      · intro a; simp
    have hbuf : S₂ .buffer = [] := by
      rw [hW _ (walk_excludes (by decide) (by decide) (by simp)), hf]
      · rfl
      · intro a; simp
    obtain ⟨w₃, S₃, r₃, o₃, s₃, f₃⟩ := embed_num .m (k.choose 2) [] w₂ S₂
      ((localCode_m _).trans hM) ⟨hbase _, hbase _, hbase _⟩ (hbase _)
    have ok₃ : S₃ (.code .O) = encodeNat (k.choose 2) := by simpa [payload, framed] using o₃
    have hk₃ : S₃ (.prep .sizeK) = cnt EmitSS.U k :=
      (f₃ _ (by intro j; cases j <;> decide)).trans hK
    obtain ⟨w₄, S₄, r₄, o₄, s₄, f₄⟩ := embed_num .k k (encodeNat (k.choose 2)) w₃ S₃
      ((localCode_k _).trans hk₃) s₃ ok₃
    have hF (j : K) (hm : ∀ a, codeSlot .m a ≠ j) (hk : ∀ a, codeSlot .k a ≠ j) :
        S₄ j = S₂ j := (f₄ j hk).trans (f₃ j hm)
    have he₄ : S₄ (.walk (.r (.edge .output))) = ed :=
      (hF _ (by intro a; cases a <;> decide) (by intro a; cases a <;> decide)).trans hE
    have hb₄ : S₄ .buffer = [] :=
      (hF _ (by intro a; cases a <;> decide) (by intro a; cases a <;> decide)).trans hbuf
    obtain ⟨w₅, S₅, r₅, o₅, f₅⟩ := assemble_edges ed _ w₄ S₄ he₄ o₄ hb₄
    have hs₅ : scratch S₅ := ⟨(f₅ _ (by decide) (by decide) (by decide)).trans s₄.1,
      (f₅ _ (by decide) (by decide) (by decide)).trans s₄.2.1,
      (f₅ _ (by decide) (by decide) (by decide)).trans s₄.2.2⟩
    have hn₅ : S₅ (.walk .d) = cnt EmitSS.U n := ((f₅ _ (by decide) (by decide) (by decide)).trans
      (hF _ (by intro j; cases j <;> decide) (by intro j; cases j <;> decide))).trans hN
    obtain ⟨w, T, r₆, o₆, -, -⟩ := embed_num .n n _ w₅ S₅ ((localCode_n _).trans hn₅) hs₅ o₅
    refine ⟨w, T, (((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).mono ?_, ?_⟩
    · have hlenE := (edgeLength_bound n bits).trans (show bits.length * (6 * n + 3) ≤
          L * (6 * L + 3) by gcongr; omega)
      have hwalk : n * (n * (1432 * n + 623) + (6 * n + 10)) + 1 ≤
          L * (L * (1432 * L + 623) + (6 * L + 10)) + 1 := by gcongr
      change (20 * (L + 1) ^ 2 + _ + (710 * k.choose 2 + 306) + (710 * k + 306) +
          (3 * ed.length + 3) + (710 * n + 306)) ≤ 6000 * (L + 1) ^ 3
      exact le_trans (by gcongr) (by nlinarith [Nat.zero_le L])
    · rw [cliqueToDensest, hd]
      simp only [hbits, ite_true]
      change T (.code .O) = delimit (encodeNat n) ++ (delimit ed ++
        (delimit (encodeNat k) ++ encodeNat (k.choose 2)))
      exact o₆

/- The assembled finite converter gives a witness in the canonical machine model. -/
theorem isPolyTime_cliqueToDensest : IsPolyTime cliqueToDensest := by
  let c : Host.Comp := {
    K := K
    Γ := Γ
    finΓ := fun j => by
      rcases j with p | w | a | _
      · cases p <;> infer_instance
      · cases w with
        | r r =>
          cases r with
          | edge e => cases e with | «local» l => cases l <;> infer_instance | _ => infer_instance
          | _ => infer_instance
        | _ => infer_instance
      · cases a <;> infer_instance
      · infer_instance
    L := Lab
    prog := prog
    ks := Finset.univ.toList
    ks_nodup := Finset.nodup_toList _
    mem_ks := by simp }
  refine Host.isPolyTime_reduction (c := c) (cX := .prep .input) (cO := .code .O)
    (gX := id) (start := .prep .rk) (done := .done) (Equiv.refl Bool)
    cliqueToDensest (Polynomial.C 6000 * (Polynomial.X + 1) ^ 3) rfl ?_
  intro x
  obtain ⟨w, S, h, ho⟩ := bounded_total x false
  have hin : update (fun j : K => ([] : List (Γ j))) (.prep .input) (x.map id) = init x := by
    funext j
    cases j with
    | prep j => cases j <;> simp [init, CliquePrepare.init]
    | _ => rfl
  change ∃ w S, RunLe prog ((Polynomial.C (6000 : ℕ) * (Polynomial.X + 1) ^ 3).eval x.length)
    ⟨some (.prep .rk), false, update (fun j : K => ([] : List (Γ j))) (.prep .input) (x.map id)⟩
    ⟨some .done, w, S⟩ ∧ S (.code .O) = (cliqueToDensest x).map (Equiv.refl Bool).symm
  rw [hin]
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Equiv.refl_symm, Equiv.coe_refl, List.map_id]
    using (⟨w, S, h, ho⟩ : ∃ w S, RunLe prog (6000 * (x.length + 1) ^ 3)
      ⟨some (.prep .rk), false, init x⟩ ⟨some .done, w, S⟩ ∧ S (.code .O) = cliqueToDensest x)

/- The exact target language is NP-hard, using the existing CLIQUE theorem. -/
theorem densest_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L densestKSubgraphDec :=
  NPHard.of_polyManyOneRed cliqueDec_npComplete.2
    ⟨cliqueToDensest, isPolyTime_cliqueToDensest, cliqueDec_eq_densestKSubgraphDec⟩

end Cslib.Complexity.DensestKSubgraph.Internal.CliqueReduction
