/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.Combinatorics.Words.CobhamUniformMorphism
public import MathlibExt.Combinatorics.Words.MetaAutomaticTwo
import Mathlib.Data.Fintype.Pi

/-!
# The pair recurrence of the second meta-automatic sequence

The two Boolean coordinates close under the four base-four digit transitions.
Reading digits in the opposite order amounts to accumulating compositions of
those transitions, rather than applying each transition to the current pair.
-/

namespace MetaMathlibExt

private theorem metaAutomaticTwo_four_mul (n : ℕ) :
    metaAutomaticTwo (4 * n) = metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat) := by
  rcases n with _ | n
  · simp [metaAutomaticTwo]
  · exact (metaAutomaticTwo_rec (n + 1)).1 (by omega)

private theorem metaAutomaticTwo_odd (n : ℕ) :
    metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) := by
  have h := metaAutomaticTwo_balanced n
  cases he : metaAutomaticTwo (2 * n) <;> simpa [he] using h

-- Once the first bit is known, the even entry recovers the second coordinate.
private theorem metaAutomaticTwo_pair_snd (s : ℕ → Bool × Bool)
    (hs : ∀ m, s m = (metaAutomaticTwo m,
      metaAutomaticTwo (2 * m + (metaAutomaticTwo m).toNat))) (n : ℕ) :
    (s n).2 = xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n)) := by
  rw [hs n, (metaAutomaticTwo_recover n).1, ← Bool.xor_assoc]
  simp

private theorem metaAutomaticTwo_other_even (n : ℕ) :
    metaAutomaticTwo (4 * n + 2) = !metaAutomaticTwo (4 * n) := by
  rw [(metaAutomaticTwo_rec n).2.2.1, metaAutomaticTwo_four_mul]
  cases h : metaAutomaticTwo n
  · simpa [h] using metaAutomaticTwo_odd n
  · simp [metaAutomaticTwo_odd n]

private theorem metaAutomaticTwo_pair_steps (s : ℕ → Bool × Bool)
    (hs : ∀ m, s m = (metaAutomaticTwo m,
      metaAutomaticTwo (2 * m + (metaAutomaticTwo m).toNat))) (n : ℕ) :
    s (4 * n) = ((s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 1) = (!(s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 2) = (!(s n).2, !xor (s n).1 (s n).2) ∧
      s (4 * n + 3) = ((s n).2, !xor (s n).1 (s n).2) := by
  have h0 : metaAutomaticTwo (4 * n) = (s n).2 := by
    rw [metaAutomaticTwo_four_mul, hs n]
  have h1 : metaAutomaticTwo (4 * n + 1) = !(s n).2 := by
    rw [show 4 * n + 1 = 2 * (2 * n) + 1 by omega, metaAutomaticTwo_odd,
      show 2 * (2 * n) = 4 * n by omega, h0]
  have h2 : metaAutomaticTwo (4 * n + 2) = !(s n).2 := by
    rw [metaAutomaticTwo_other_even, h0]
  have h3 : metaAutomaticTwo (4 * n + 3) = (s n).2 := by
    rw [(metaAutomaticTwo_rec n).2.2.2, h2, Bool.not_not]
  have ⟨he, ho⟩ : metaAutomaticTwo (2 * n) = xor (s n).1 (s n).2 ∧
      metaAutomaticTwo (2 * n + 1) = !xor (s n).1 (s n).2 := by
    rw [hs n]
    exact metaAutomaticTwo_recover n
  have hfour (m : ℕ) : metaAutomaticTwo (4 * m) =
      xor (metaAutomaticTwo m) (metaAutomaticTwo (2 * m)) := by
    rw [metaAutomaticTwo_four_mul, ← metaAutomaticTwo_pair_snd s hs m, hs m]
  have he₀ : metaAutomaticTwo (2 * (4 * n)) = xor (xor (s n).1 (s n).2) (s n).2 := by
    rw [show 2 * (4 * n) = 4 * (2 * n) by omega, hfour,
      show 2 * (2 * n) = 4 * n by omega, he, h0]
  have he₂ : metaAutomaticTwo (2 * (4 * n + 2)) = xor (!xor (s n).1 (s n).2) (!(s n).2) := by
    rw [show 2 * (4 * n + 2) = 4 * (2 * n + 1) by omega, hfour,
      show 2 * (2 * n + 1) = 4 * n + 2 by omega, ho, h2]
  have he₁ : metaAutomaticTwo (2 * (4 * n + 1)) = !metaAutomaticTwo (2 * (4 * n)) := by
    rw [show 2 * (4 * n + 1) = 4 * (2 * n) + 2 by omega, metaAutomaticTwo_other_even,
      show 4 * (2 * n) = 2 * (4 * n) by omega]
  have he₃ : metaAutomaticTwo (2 * (4 * n + 3)) = !metaAutomaticTwo (2 * (4 * n + 2)) := by
    rw [show 2 * (4 * n + 3) = 4 * (2 * n + 1) + 2 by omega, metaAutomaticTwo_other_even,
      show 4 * (2 * n + 1) = 2 * (4 * n + 2) by omega]
  refine ⟨Prod.ext (by rw [hs, h0]) ?_, Prod.ext (by rw [hs, h1]) ?_,
    Prod.ext (by rw [hs, h2]) ?_, Prod.ext (by rw [hs, h3]) ?_⟩
  · rw [metaAutomaticTwo_pair_snd s hs, h0, he₀]
    cases (s n).1 <;> cases (s n).2 <;> rfl
  · rw [metaAutomaticTwo_pair_snd s hs, h1, he₁, he₀]
    cases (s n).1 <;> cases (s n).2 <;> rfl
  · rw [metaAutomaticTwo_pair_snd s hs, h2, he₂]
    cases (s n).1 <;> cases (s n).2 <;> rfl
  · rw [metaAutomaticTwo_pair_snd s hs, h3, he₃, he₂]
    cases (s n).1 <;> cases (s n).2 <;> rfl

private def pairCode (p : Bool × Bool) : Fin 4 :=
  ⟨p.1.toNat + 2 * p.2.toNat, by rcases p with ⟨x, y⟩; cases x <;> cases y <;> decide⟩

private def pairDecode (q : Fin 4) : Bool × Bool := (q.val % 2 == 1, q.val / 2 == 1)

private theorem pairDecode_pairCode (p : Bool × Bool) : pairDecode (pairCode p) = p := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;> rfl

private def affineStep (q d : Fin 4) : Fin 4 :=
  let (x, y) := pairDecode q
  let z := xor x y
  pairCode (match d.val with
    | 0 => (y, z)
    | 1 => (!y, z)
    | 2 => (!y, !z)
    | _ => (y, !z))

private theorem baseWordValueLSD_map_ofNat (ds : List ℕ) (hd : ∀ d ∈ ds, d < 4) :
    baseWordValueLSD (ds.map (Fin.ofNat 4)) = Nat.ofDigits 4 ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have h := hd d (List.mem_cons_self ..)
    have htail := ih (fun e he => hd e (List.mem_cons_of_mem _ he))
    change d % 4 + 4 * baseWordValueLSD (ds.map (Fin.ofNat 4)) = d + 4 * Nat.ofDigits 4 ds
    rw [Nat.mod_eq_of_lt h, htail]

/-- **Pair recurrence and $4$-automaticity of $\mathcal{M}_2$.** Read the meta-automatic
sequence $\mathcal{M}_2$ as taking values in $\{0, 1\}$, write $\oplus$ for addition modulo $2$,
and let $s(n) = (\mathcal{M}_2(n), \mathcal{M}_2(2n + \mathcal{M}_2(n)))$. For every $n \ge 0$,
writing $s(n) = (x, y)$, we have $s(4n) = (y, x \oplus y)$, $s(4n+1) = (y \oplus 1, x \oplus y)$,
$s(4n+2) = (y \oplus 1, x \oplus y \oplus 1)$ and $s(4n+3) = (y, x \oplus y \oplus 1)$.
Moreover, $\mathcal{M}_2$ is $4$-automatic, and it is computed by a four-state automaton: there
are maps $\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ and
$\tau : \{0, 1, 2, 3\} \to \{0, 1\}$ such that for every $n$, $\mathcal{M}_2(n) = \tau(q)$, where
$q$ is the state reached from the state $0$ by reading the base-$4$ digits of $n$ with $\delta$,
most significant digit first (for $n = 0$ no digit is read, so $q = 0$).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 20 (`jis-2026-26.4.1-thm-20`). -/
public theorem metaAutomaticTwo_affine (s : ℕ → Bool × Bool)
    (hs : ∀ m, s m = (metaAutomaticTwo m,
      metaAutomaticTwo (2 * m + (metaAutomaticTwo m).toNat))) :
    (∀ n, s (4 * n) = ((s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 1) = (!(s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 2) = (!(s n).2, !xor (s n).1 (s n).2) ∧
      s (4 * n + 3) = ((s n).2, !xor (s n).1 (s n).2)) ∧
    IsKAutomaticSequence 4 metaAutomaticTwo ∧
    ∃ δ : Fin 4 → Fin 4 → Fin 4, ∃ τ : Fin 4 → Bool, ∀ n,
      metaAutomaticTwo n =
        τ ((Nat.digits 4 n).reverse.foldl (fun q d => δ q (Fin.ofNat 4 d)) 0) := by
  have hpair := metaAutomaticTwo_pair_steps s hs
  have hstep (n : ℕ) (d : Fin 4) : affineStep (pairCode (s n)) d =
      pairCode (s (4 * n + d.val)) := by
    obtain ⟨h0, h1, h2, h3⟩ := hpair n
    have hd : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 := by omega
    rcases hd with hd | hd | hd | hd <;>
      simp only [affineStep, pairDecode_pairCode, hd, Nat.add_zero, h0, h1, h2, h3]
  have hout (n : ℕ) : (pairDecode (pairCode (s n))).1 = metaAutomaticTwo n := by
    rw [pairDecode_pairCode, hs n]
  -- This invariant holds for all words, including words padded with high-order zeros.
  have hfold (ds : List (Fin 4)) : ds.reverse.foldl affineStep 0 =
      pairCode (s (baseWordValueLSD ds)) := by
    induction ds with
    | nil =>
      change (0 : Fin 4) = pairCode (s 0)
      simp [hs, pairCode, metaAutomaticTwo]
    | cons d ds ih =>
      rw [List.reverse_cons, List.foldl_append, ih]
      change affineStep (pairCode (s (baseWordValueLSD ds))) d =
        pairCode (s (d.val + 4 * baseWordValueLSD ds))
      rw [Nat.add_comm, hstep]
  refine ⟨hpair, ?_, affineStep, fun q => (pairDecode q).1, ?_⟩
  · -- The definition of automaticity reads least significant digits first.
    let trans (f : Fin 4 → Fin 4) (d : Fin 4) (q : Fin 4) := f (affineStep q d)
    have hcomp (ds : List (Fin 4)) (f : Fin 4 → Fin 4) :
        ds.foldl trans f 0 = f (ds.reverse.foldl affineStep 0) := by
      induction ds generalizing f with
      | nil => rfl
      | cons d ds ih =>
        rw [List.foldl_cons, ih, List.reverse_cons, List.foldl_append]
        rfl
    let e := Fintype.equivFin (Fin 4 → Fin 4)
    let step (q : Fin (Fintype.card (Fin 4 → Fin 4))) (d : Fin 4) := e (trans (e.symm q) d)
    have htransport (ds : List (Fin 4)) (f : Fin 4 → Fin 4) :
        ds.foldl step (e f) = e (ds.foldl trans f) := by
      induction ds generalizing f with
      | nil => rfl
      | cons d ds ih =>
        simpa only [List.foldl_cons, step, Equiv.symm_apply_apply] using ih (trans f d)
    refine ⟨by decide, _, Fintype.card_pos_iff.mpr ⟨id⟩, e id, step,
      fun q => (pairDecode (e.symm q 0)).1, ?_⟩
    intro n ds hds
    change (pairDecode (e.symm (ds.foldl step (e id)) 0)).1 = metaAutomaticTwo n
    rw [htransport, Equiv.symm_apply_apply, hcomp, id_eq, hfold, hds, hout]
  · intro n
    change metaAutomaticTwo n = (pairDecode
      ((Nat.digits 4 n).reverse.foldl (fun q d => affineStep q (Fin.ofNat 4 d)) 0)).1
    rw [← List.foldl_map, List.map_reverse, hfold, baseWordValueLSD_map_ofNat,
      Nat.ofDigits_digits, hout]
    exact fun d hd => Nat.digits_lt_base (by decide) hd

end MetaMathlibExt
