/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.CookLevin.Precompute
import CSLibExt.Computability.Complexity.Host
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy

/-!
# RP is contained in NP

An accepting random tape serves as an NP certificate. The verifier computes the RP tape length
by Horner's rule and reads exactly that many certificate bits, supplying false for missing bits.
-/

public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RPSubsetNP

open Turing Function TM2Program TM2Embedding
open Cslib.Complexity Cslib.Complexity.DenseSAT Cslib.Complexity.Classes
open Cslib.Complexity.CookLevin.CounterView Cslib.Complexity.CookLevin.Precompute
open ComplexityTheory

-- Pushing each bit onto the output stack reverses the tape. A certificate can supply its reverse.
private def coins (n : ℕ) (w : List Bool) : List Bool :=
  (w.take n ++ List.replicate (n - w.length) false).reverse

private theorem length_coins (n : ℕ) (w : List Bool) : (coins n w).length = n := by
  simp [coins]

private theorem coins_reverse (w : List Bool) : coins w.length w.reverse = w := by
  simp [coins, List.take_of_length_le (show w.reverse.length ≤ w.length by simp)]

/-! ### Normalizing the certificate on tagged pairs -/

private inductive Counter | base | acc | prod | index | scratch
  deriving DecidableEq

private instance counterFintype : Fintype Counter where
  elems := ⟨↑[Counter.base, .acc, .prod, .index, .scratch], by decide⟩
  complete k := by cases k <;> decide

private abbrev Round (cs : List ℕ) := Option (Fin cs.length × HW)

private def roundAt (cs : List ℕ) (i : ℕ) (s : HW) : Round cs :=
  if h : i < cs.length then some (⟨i, h⟩, s) else none

private def rounds (cs : List ℕ) : Round cs → TM2.Stmt (SΓ Counter) (Round cs) Bool
  | none => .halt
  | some (i, s) => hornS .base .acc .prod .index .scratch cs[i] (roundAt cs i)
      (roundAt cs (i + 1) (.mul .head)) s

private inductive Stack | work (k : SK Counter) | input | output
  deriving DecidableEq, Fintype

private abbrev Γ : Stack → Type
  | .work k => SΓ Counter k
  | .input | .output => Verifier.G

private def emb : SEmb (SΓ Counter) Γ where
  e := .work
  inj := fun _ _ => Stack.work.inj
  ι _ := Equiv.refl _

private inductive Lab (cs : List ℕ)
  | read | sep | eval (r : Round cs) | clean | join | restore | done
  deriving DecidableEq, Fintype

private abbrev count (k : Counter) := Stack.work (.c k)
private abbrev saved := Stack.work .out
private abbrev tag (b : Bool) : Verifier.G := .inr (some b)

-- Save the input word while counting its bits. The final Horner accumulator controls how
-- many bits to push from the certificate. Then restore the separator and the saved word.
private def prog (cs : List ℕ) : Lab cs → TM2.Stmt Γ (Lab cs) Bool
  | .read => PolynomialEncoding.splitB .input saved (count .base) Host.dX id (fun _ => ())
      .read .sep
  | .sep => .pop .input (fun _ _ => false) (.goto fun _ => .eval (roundAt cs 0 (.mul .head)))
  | .eval (some r) => mapS emb Lab.eval (rounds cs (some r))
  | .eval none => .pop (count .acc) (fun _ o => o.isSome) <| .branch id
      (.pop .input (fun _ o => (o.bind Host.dW).getD false) <|
        .push .output tag (.goto fun _ => .eval none))
      (.goto fun _ => .clean)
  | .clean => cleanS [.input, count .base] .clean .join
  | .join => .push .output (fun _ => .inr none) (.goto fun _ => .restore)
  | .restore => moveB saved .output some Sum.inl .restore .done
  | .done => .load (fun _ => false) .halt

private abbrev tm (cs : List ℕ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Γ
  Λ := Lab cs
  main := .read
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Verifier.G)
  m := prog cs

private def counters (n m : ℕ) : Counter → ℕ
  | .base => n
  | .acc => m
  | _ => 0

private def layout (n m : ℕ) (x : List Bool) (i o : List Verifier.G) :
    (k : Stack) → List (Γ k)
  | .work k => st (counters n m) x k
  | .input => i
  | .output => o

private theorem read_run (cs : List ℕ) (x w : List Bool) :
    Run (prog cs) (x.length + 2)
      (initList (tm cs) (Verifier.pairEncode (x, w)))
      ⟨some (.eval (roundAt cs 0 (.mul .head))), false,
        layout x.length 0 x.reverse (w.map tag) []⟩ := by
  let S := layout 0 0 [] (Verifier.pairEncode (x, w)) []
  obtain ⟨T, hr, hi, hx, hn, hk⟩ := PolynomialEncoding.splitB_run (M := prog cs)
    (a := .input) (b := saved) (c := count .base) (d := Host.dX) (gb := id) (gc := fun _ => ())
    (self := .read) (next := .sep) rfl (by decide) (by decide) (by decide)
    Sum.inl (fun _ => rfl) x (.inr none :: w.map tag) false S rfl rfl
  have hT : T = layout x.length 0 x.reverse (.inr none :: w.map tag) [] := by
    funext k
    rcases k with (_ | k) | _ | _
    · simpa [S, layout] using hx
    · cases k with
      | base => simpa [S, layout, counters, cnt, List.map_const'] using hn
      | _ => exact hk _ (by decide) (by decide) (by decide)
    · exact hi
    · exact hk _ (by decide) (by decide) (by decide)
  rw [hT] at hr
  have hs : Run (prog cs) 1
      ⟨some .sep, false, layout x.length 0 x.reverse (.inr none :: w.map tag) []⟩
      ⟨some (.eval (roundAt cs 0 (.mul .head))), false,
        layout x.length 0 x.reverse (w.map tag) []⟩ := by
    apply Run.single
    apply congrArg (TM2.Cfg.mk _ false)
    funext k
    cases k <;> rfl
  have hinit : (initList (tm cs) (Verifier.pairEncode (x, w))).stk = S := by
    funext k
    rcases k with (_ | k) | _ | _
    · rfl
    · cases k <;> rfl
    · rfl
    · rfl
  change Run _ _ ⟨_, _, _⟩ _
  rw [← hinit] at hr
  exact (hr.trans hs).of_eq (by omega)

private theorem eval_run (p : Polynomial ℕ) (n : ℕ) (x : List Bool) (i : List Verifier.G) :
    ∃ v, Run (prog (coeffs p)) (hornT (coeffs p) n 0)
      ⟨some (.eval (roundAt (coeffs p) 0 (.mul .head))), false, layout n 0 x i []⟩
      ⟨some (.eval none), v, layout n (p.eval n) x i []⟩ := by
  let cs := coeffs p
  have hat (j : ℕ) : (if j < cs.length then roundAt cs j (.mul .head) else none) =
      roundAt cs j (.mul .head) := by by_cases h : j < cs.length <;> simp [roundAt, h]
  obtain ⟨v, hr⟩ := horner_run (M := rounds cs) (b := .base) (acc := .acc) (q := .prod)
    (ad := .index) (t := .scratch) cs (mk := roundAt cs) (exit := none)
    (fun j hj s => by rw [hat, roundAt, dite_eq_left hj]; rfl) (by decide)
    cs.length 0 (by simp) (counters n 0) rfl rfl rfl false x
  rw [hat, List.drop_zero] at hr
  change Run _ (hornT cs n 0) _ ⟨_, v, st (update (counters n 0) .acc (hornVal cs n 0)) x⟩ at hr
  rw [hornVal_coeffs] at hr
  have hF : update (counters n 0) .acc (p.eval n) = counters n (p.eval n) := by
    funext k
    cases k <;> rfl
  rw [hF] at hr
  have embeds : Embeds emb Lab.eval (rounds cs) (prog cs) := by
    intro l
    cases l with
    | none => exact Or.inr rfl
    | some r => exact Or.inl rfl
  obtain ⟨T, run, ha, hf⟩ := run_embed Lab.eval embeds _ _ _ _ _ _ _ (layout n 0 x i []) hr
    (fun k => (List.map_id _).symm)
  have hT : T = layout n (p.eval n) x i [] := by
    funext k
    rcases k with k | _ | _
    · exact (ha k).trans (List.map_id _)
    · exact hf _ (fun _ => by simp [emb])
    · exact hf _ (fun _ => by simp [emb])
  exact ⟨v, hT ▸ run⟩

private theorem fill_run (cs : List ℕ) (n m : ℕ) (x w : List Bool) (o : List Verifier.G)
    (v : Bool) :
    Run (prog cs) (m + 1)
      ⟨some (.eval none), v, layout n m x (w.map tag) o⟩
      ⟨some .clean, false, layout n 0 x ((w.drop m).map tag) ((coins m w).map tag ++ o)⟩ := by
  induction m generalizing w o v with
  | zero =>
    simp only [coins, List.take_zero, Nat.zero_sub, List.replicate_zero, List.append_nil,
      List.reverse_nil, List.map_nil, List.nil_append, List.drop_zero]
    apply Run.single
    apply congrArg (TM2.Cfg.mk _ false)
    funext k
    rcases k with (_ | k) | _ | _ <;> try rfl
    cases k <;> rfl
  | succ m ih =>
    let b := w.headD false
    have step : Run (prog cs) 1
        ⟨some (.eval none), v, layout n (m + 1) x (w.map tag) o⟩
        ⟨some (.eval none), b, layout n m x (w.tail.map tag) (tag b :: o)⟩ := by
      apply Run.single
      cases w <;> apply congrArg (TM2.Cfg.mk _ _) <;> funext k <;>
        rcases k with (_ | k) | _ | _ <;> first | rfl | cases k <;> rfl
    have hcoins : coins (m + 1) w = coins m w.tail ++ [b] := by
      cases w <;> simp [coins, b, List.replicate_succ, List.reverse_cons]
    rw [hcoins, List.map_append, List.append_assoc]
    rw [show w.drop (m + 1) = w.tail.drop m by cases w <;> simp]
    exact (step.trans (ih w.tail (tag b :: o) b)).of_eq (by omega)

private theorem finish_run (cs : List ℕ) (x : List Bool) (i : List Verifier.G) (r : List Bool) :
    RunLe (prog cs) (2 * x.length + i.length + 4)
      ⟨some .clean, false, layout x.length 0 x.reverse i (r.map tag)⟩
      (haltList (tm cs) (Verifier.pairEncode (x, r))) := by
  have hc := clean_run (M := prog cs) (ks := [.input, count .base])
    (self := .clean) (next := .join) rfl (by decide) (x.length + i.length) false
    (layout x.length 0 x.reverse i (r.map tag)) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> simp [layout, count, counters, cnt])
  have hclean : (fun k => if k ∈ [Stack.input, count .base] then [] else
      layout x.length 0 x.reverse i (r.map tag) k) = layout 0 0 x.reverse [] (r.map tag) := by
    funext k
    rcases k with (_ | k) | _ | _ <;> try rfl
    cases k <;> rfl
  rw [hclean] at hc
  have hj : Run (prog cs) 1 ⟨some .join, false, layout 0 0 x.reverse [] (r.map tag)⟩
      ⟨some .restore, false, layout 0 0 x.reverse [] (.inr none :: r.map tag)⟩ := by
    apply Run.single
    apply congrArg (TM2.Cfg.mk _ false)
    funext k
    cases k <;> rfl
  obtain ⟨v, S, hr, hx, ho, hk⟩ := moveB_run (M := prog cs) (a := saved) (b := .output)
    (self := .restore) (next := .done) (d := some) (g := Sum.inl) rfl (by decide)
    x.reverse x.reverse [] false (layout 0 0 x.reverse [] (.inr none :: r.map tag))
    (by simp [layout]) rfl rfl
  have hS : S = (haltList (tm cs) (Verifier.pairEncode (x, r))).stk := by
    funext k
    rcases k with (_ | k) | _ | _
    · exact hx
    · exact (hk _ (by simp [saved]) (by simp)).trans (by cases k <;> rfl)
    · exact hk _ (by decide) (by decide)
    · simpa [layout, Verifier.pairEncode, tag, List.map_reverse, Host.haltList_eq, tm] using ho
  have hd : Run (prog cs) 1 ⟨some .done, v, S⟩
      (haltList (tm cs) (Verifier.pairEncode (x, r))) := by
    rw [hS]
    exact Run.single rfl
  exact (hc.trans ((hj.trans (hr.trans hd)).le le_rfl)).mono (by simp; omega)

private def normalize (p : Polynomial ℕ) (q : List Bool × List Bool) : List Bool × List Bool :=
  (q.1, coins (p.eval q.1.length) q.2)

private theorem isPolyTime_normalize (p : Polynomial ℕ) : IsPolyTime (normalize p) := by
  obtain ⟨h, hh⟩ := IsPoly.hornT (coeffs p) (IsPoly.const 0)
  let time := h + p + Polynomial.C 3 * Polynomial.X + Polynomial.C 7
  let machine : TM2ComputableInPolyTime Verifier.pairEncode Verifier.pairEncode (normalize p) :=
    { tm := tm (coeffs p)
      inputAlphabet := Equiv.refl _
      outputAlphabet := Equiv.refl _
      time := time
      outputsFun := fun ⟨x, w⟩ => Classical.choice <| by
        let m := p.eval x.length
        obtain ⟨v, he⟩ := eval_run p x.length x.reverse (w.map tag)
        have hr := ((read_run (coeffs p) x w).trans he).trans
          (fill_run (coeffs p) x.length m x.reverse w [] v)
        simp only [List.append_nil] at hr
        obtain ⟨t, ht, run⟩ := (hr.le le_rfl).trans
          (finish_run (coeffs p) x ((w.drop m).map tag) (coins m w))
        refine ⟨⟨⟨t, ?_⟩, ?_⟩⟩
        · change Run (prog (coeffs p)) t
            (initList (tm (coeffs p)) ((Verifier.pairEncode (x, w)).map id))
            (haltList (tm (coeffs p)) ((Verifier.pairEncode (normalize p (x, w))).map id))
          erw [List.map_id, List.map_id]
          exact run
        · change t ≤ time.eval (Verifier.pairEncode (x, w)).length
          have hx : x.length ≤ (Verifier.pairEncode (x, w)).length := by simp [Verifier.pairEncode]
          have hh' := TM2Composition.eval_mono h hx
          have hp := TM2Composition.eval_mono p hx
          rw [← hh x.length] at hh'
          simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          simp only [Verifier.pairEncode, List.length_append, List.length_map, List.length_cons,
            List.length_drop] at ht hh' hp ⊢
          dsimp [m] at ht
          omega }
  obtain ⟨h₁⟩ := tm2ComputableInPolyTime_comp Converter.computable machine
  exact tm2ComputableInPolyTime_comp h₁ ToCanonical.computable

/-- **RP is contained in NP.** Every decision problem in the class $\mathsf{RP}$ of
one-sided-error randomized polynomial-time decision problems also belongs to the class
$\mathsf{NP}$.

Source: S. Arora and B. Barak, Computational Complexity:
A Modern Approach, 2009, Theorem 7.3 (RP ⊆ NP); M. Sipser, Introduction to the
Theory of Computation, 3rd ed., 2013, Theorem 10.13. -/
public theorem rp_subset_np :
    RP ⊆ NP := by
  rintro L ⟨p, R, hR, hL⟩
  refine ⟨p, R ∘ normalize p, (isPolyTime_normalize p).comp hR, fun x => ?_⟩
  let m := p.eval x.length
  let A : Set (Fin m → Bool) := {r | R (x, List.ofFn r) = true}
  constructor
  · intro hx
    have hy : 2 ^ m ≤ 2 * A.ncard := (hL x).1 hx
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos _
    obtain ⟨r, hr⟩ := (Set.ncard_pos (s := A)).mp (by omega)
    refine ⟨(List.ofFn r).reverse, by simp [m], ?_⟩
    change R (x, coins m (List.ofFn r).reverse) = true
    have hcoins := coins_reverse (List.ofFn r)
    rw [List.length_ofFn] at hcoins
    rw [hcoins]
    exact hr
  · rintro ⟨w, _, hw⟩
    by_contra! hx
    have hzero : A.ncard = 0 := (hL x).2 (Bool.eq_false_iff.mpr hx)
    have hrepr {m : ℕ} (u : List Bool) (hu : u.length = m) :
        ∃ r : Fin m → Bool, List.ofFn r = u := by
      subst m
      exact ⟨u.get, List.ofFn_get u⟩
    obtain ⟨r, hr⟩ := hrepr (coins m w) (length_coins m w)
    have ha : r ∈ A := by
      change R (x, List.ofFn r) = true
      rw [hr]
      exact hw
    exact Set.ncard_ne_zero_of_mem ha A.toFinite hzero

end MetaMathlibExt.Complexity.KeyTheorems.RPSubsetNP
