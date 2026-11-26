/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
public import MathlibExt.Computability.BinaryNatEncoding

/-! # One canonical edge frame emitted from physical unary counters -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.EmitEdge

open Turing MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier (Sym)
open Computability (encodeNat)

/- The two counters share an encoder workspace, with separate framing and output stacks. -/
inductive K | local (k : EmitSS.K) | second | buffer | output
  deriving DecidableEq

instance : Fintype K where
  elems := {K.second, .buffer, .output} ∪ Finset.univ.image K.local
  complete k := by cases k <;> simp

/- The unary encoder's heterogeneous workspace and two Boolean output stacks. -/
@[reducible] def Γ : K → Type
  | .local k => EmitSS.Γ k
  | .second => Sym
  | .buffer | .output => Bool

/- Convert the second endpoint raw, prepend the first framed, and frame the resulting pair. -/
inductive Lab | code (first : Bool) (l : UnaryNat.Lab) | frame | write | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.frame, .write, .done} ∪ Finset.univ.image (Lab.code false) ∪
    Finset.univ.image (Lab.code true)
  complete l := by cases l with | code b l => cases b <;> simp | _ => simp

/- Only the counter itself is rerouted for the second endpoint. -/
def place (first : Bool) (k : EmitSS.K) : K :=
  if !first && k == .A then .second else .local k

/- Embed either encoder in exactly the same work tape layout except for its counter. -/
def emb (first : Bool) : SEmb EmitSS.Γ Γ where
  e := place first
  inj a b h := by cases first <;> cases a <;> cases b <;> cases h <;> rfl
  ι k := by cases first <;> cases k <;> exact Equiv.refl _

/- The raw second endpoint is immediately followed by the framed first endpoint. -/
def redirect (first : Bool) : UnaryNat.Lab → Lab
  | .done => if first then .frame else .code true (.emit .hv)
  | l => .code first l

/- The two conversions and the final wrapping form one bounded finite program. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .code first l => mapS (emb first) (redirect first) (UnaryNat.prog first l)
  | .frame => emitFrame (.local .O) .buffer some id .frame .write
  | .write => moveB .buffer .output some id .write .done
  | .done => .halt

private theorem embeds (first : Bool) : Embeds (emb first) (redirect first) (UnaryNat.prog first)
    prog := by
  intro l
  cases l with
  | emit | clean | read | back => exact Or.inl rfl
  | done => exact Or.inr rfl

private def pull (first : Bool) (S : ∀ k, List (Γ k)) : ∀ k, List (EmitSS.Γ k) :=
  fun k => (S ((emb first).e k)).map ((emb first).ι k).symm

private theorem agree_pull (first : Bool) (S : ∀ k, List (Γ k)) :
    Agree (emb first) (pull first S) S := by
  intro k
  simp [pull, List.map_map, Function.comp_def]

private theorem pull_true (S : ∀ k, List (Γ k)) (k : EmitSS.K) :
    pull true S k = S (.local k) := by
  cases k <;> exact List.map_id _

private theorem pull_false (S : ∀ k, List (Γ k)) (k : EmitSS.K) (hk : k ≠ .A) :
    pull false S k = S (.local k) := by
  cases k <;> first | contradiction | exact List.map_id _

private theorem pull_false_A (S : ∀ k, List (Γ k)) : pull false S .A = S .second :=
  List.map_id _

private theorem agree_true {T : ∀ k, List (EmitSS.Γ k)} {S : ∀ k, List (Γ k)}
    (h : Agree (emb true) T S) (k : EmitSS.K) : S (.local k) = T k := by
  have hh := h k
  cases k <;> exact hh.trans (List.map_id _)

private theorem agree_false {T : ∀ k, List (EmitSS.Γ k)} {S : ∀ k, List (Γ k)}
    (h : Agree (emb false) T S) (k : EmitSS.K) (hk : k ≠ .A) : S (.local k) = T k := by
  have hh := h k
  cases k <;> first | contradiction | exact hh.trans (List.map_id _)

private theorem agree_false_A {T : ∀ k, List (EmitSS.Γ k)} {S : ∀ k, List (Γ k)}
    (h : Agree (emb false) T S) : S .second = T .A := (h .A).trans (List.map_id _)

/- Emit one edge frame in correctly oriented canonical tuple/list format, above any suffix. -/
theorem run (u v : ℕ) (out : List Bool) (flag : Bool) (S : ∀ k, List (Γ k))
    (hu : S (.local .A) = cnt EmitSS.U u) (hv : S .second = cnt EmitSS.U v)
    (hh : S (.local .H) = []) (ht : S (.local .T) = []) (hx : S (.local .X) = [])
    (ho : S (.local .O) = []) (hb : S .buffer = []) (hout : S .output = out) :
    ∃ w R, RunLe prog (714 * (u + v) + 616)
      ⟨some (.code false (.emit .hv)), flag, S⟩ ⟨some .done, w, R⟩ ∧
      R .output = delimit (bitEncode (u, v)) ++ out ∧
      R (.local .A) = [] ∧ R .second = [] ∧ R (.local .H) = [] ∧ R (.local .T) = [] ∧
      R (.local .X) = [] ∧ R (.local .O) = [] ∧ R .buffer = [] ∧
      ∀ k, k ≠ .A → k ≠ .O → k ≠ .H → k ≠ .T → k ≠ .X → R (.local k) = S (.local k) := by
  obtain ⟨f, U, hU, hUo, hUa, hUh, hUt, hUx, hUf⟩ := UnaryNat.run_raw v [] flag (pull false S)
    (by simpa only [pull_false_A] using hv)
    ((pull_false S .H (by decide)).trans hh) ((pull_false S .T (by decide)).trans ht)
    ((pull_false S .O (by decide)).trans ho) ((pull_false S .X (by decide)).trans hx)
  obtain ⟨S₁, r₁, a₁, f₁⟩ := runLe_embed (redirect false) (embeds false) hU (agree_pull false S)
  have h₁a := f₁ (.local .A) (by intro k; cases k <;> decide)
  have h₁o : S₁ (.local .O) = encodeNat v :=
    (agree_false a₁ .O (by decide)).trans (by simpa using hUo)
  obtain ⟨V, hV, hVo, hVa, hVh, hVt, hVf⟩ := UnaryNat.run_framed u (encodeNat v) f (pull true S₁)
    (by rw [pull_true, h₁a, hu])
    ((pull_true S₁ .H).trans ((agree_false a₁ .H (by decide)).trans hUh))
    ((pull_true S₁ .T).trans ((agree_false a₁ .T (by decide)).trans hUt))
    ((pull_true S₁ .O).trans h₁o)
  obtain ⟨S₂, r₂, a₂, f₂⟩ := runLe_embed (redirect true) (embeds true) hV (agree_pull true S₁)
  let p := delimit (encodeNat u) ++ encodeNat v
  have h₂o : S₂ (.local .O) = p := (agree_true a₂ .O).trans hVo
  obtain ⟨S₃, r₃, h₃o, h₃b, h₃f⟩ := emitFrame_run (M := prog) (a := K.local .O)
    (b := K.buffer) (self := Lab.frame) (next := Lab.write) (d := some) (g := id)
    rfl (by decide) id (fun _ => rfl) p [] false S₂ rfl (by simpa using h₂o)
  have h₃b' : S₃ .buffer = (delimit p).reverse := by
    rw [h₃b, f₂ .buffer (by intro k; cases k <;> decide),
      f₁ .buffer (by intro k; cases k <;> decide), hb]
    simp
  obtain ⟨w, R, r₄, h₄b, h₄o, h₄f⟩ := moveB_run (M := prog)
    (a := K.buffer) (b := K.output) (self := Lab.write) (next := Lab.done) (d := some) (g := id)
    rfl (by decide) (delimit p).reverse (delimit p).reverse [] false S₃ (by simpa using h₃b')
    rfl rfl
  have hrest (k : K) (hkl : k ≠ .local .O) (hkb : k ≠ .buffer) (hko : k ≠ .output) :
      R k = S₂ k := (h₄f _ hkb hko).trans (h₃f _ hkl hkb)
  refine ⟨w, R, (((r₁.trans r₂).trans (r₃.le le_rfl)).trans (r₄.le le_rfl)).mono ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, h₄f _ (by decide) (by decide) |>.trans h₃o, h₄b, ?_⟩
  · have hlen : p.length ≤ 2 * u + v + 1 := by
      simp only [p, List.length_append, length_delimit]
      have h₁ := EmitSS.encodeNat_length_le u
      have h₂ := EmitSS.encodeNat_length_le v
      omega
    rw [List.length_reverse, length_delimit]
    omega
  · rw [h₄o, h₃f .output (by decide) (by decide), f₂ .output (by intro k; cases k <;> decide),
      f₁ .output (by intro k; cases k <;> decide), hout]
    simp only [List.map_id_fun, id_eq, List.reverse_reverse]
    rfl
  · exact (hrest _ (by decide) (by decide) (by decide)).trans ((agree_true a₂ .A).trans hVa)
  · exact (hrest _ (by decide) (by decide) (by decide)).trans
      ((f₂ .second (by intro k; cases k <;> decide)).trans ((agree_false_A a₁).trans hUa))
  · exact (hrest _ (by decide) (by decide) (by decide)).trans ((agree_true a₂ .H).trans hVh)
  · exact (hrest _ (by decide) (by decide) (by decide)).trans ((agree_true a₂ .T).trans hVt)
  · rw [hrest _ (by decide) (by decide) (by decide), agree_true a₂ .X,
      hVf .X (by decide) (by decide) (by decide) (by decide), pull_true,
      agree_false a₁ .X (by decide), hUx]
  · intro k hk hko hkh hkt hkx
    rw [hrest _ (by simpa using hko) (by simp) (by simp), agree_true a₂ k,
      hVf k hk hkh hkt hko, pull_true, agree_false a₁ k hk, hUf k hk hkh hkt hko hkx,
      pull_false S k hk]

end Cslib.Complexity.DensestKSubgraph.Internal.EmitEdge
