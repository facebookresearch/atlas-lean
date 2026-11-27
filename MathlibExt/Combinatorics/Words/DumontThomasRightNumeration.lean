/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.DumontThomasProperPrefix
import all MathlibExt.Combinatorics.PalindromicRecurrentOutsideP
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Dumont–Thomas numeration for a right-infinite fixed point

For a non-erasing substitution and a right-infinite fixed point with growing seed $a$, every
prefix of length $n \ge 1$ has a unique $a$-admissible expansion with nonempty top word. The
fixed-point hypothesis says that the image of each finite prefix is again a prefix. This
formulation works for arbitrary alphabets, beyond the finite alphabets in the source.

## References

* Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*,
  INTEGERS 24 (2024), Article A112, pp. 1–27, Theorem 3.2 (p. 6). The proof uses Lemmas
  3.3–3.5 (p. 7), the existence argument of Lemma 3.9 (pp. 8–9), and the length crossing
  from the proof of Theorem 4.1 (pp. 11–12) with period one.
* Jean-Marie Dumont and Alain Thomas, *Systèmes de numération et fonctions fractales relatifs
  aux substitutions*, Theoretical Computer Science 65 (2) (1989), pp. 153–169, Theorem 1.5
  and Lemmas 1.1, 1.3 and 1.4.
* The proof reuses `properPrefix_morphIterate_decomposition` from
  `MathlibExt.Combinatorics.Words.DumontThomasProperPrefix`,
  `admissibleSequence_weightedLength_lt` and `letterAdmissibleSequence_eq_of_weightedLength_eq`
  from `MathlibExt.Combinatorics.Words.DumontThomasNumeration`, and `iterate_succ_right` and
  `iterate_prefix` from `MathlibExt.Combinatorics.PalindromicRecurrentOutsideP`.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted (iterate_succ_right iterate_prefix)

/-- **Dumont–Thomas numeration.** Let $\eta$ be a substitution on an alphabet $A$, extended
to finite words by concatenation, and let $u_0 u_1 u_2 \cdots$ be a right-infinite word over
$A$ that is a fixed point of $\eta$ in the sense that $\eta(u_0 \cdots u_{n-1})$ is a prefix of
$u_0 u_1 u_2 \cdots$ for every $n$. Suppose that $a = u_0$ is a growing letter, i.e.
$|\eta^k(a)| \to \infty$. Then for every $n \ge 1$ there are a natural number $k$ and an
$a$-admissible sequence $(m_i, a_i)_{0 \le i \le k}$ of pairs of a finite word and a letter
such that $m_k$ is nonempty and $u_0 \cdots u_{n-1} = \eta^k(m_k) \cdots \eta^0(m_0)$.
Moreover, if $k'$ and an $a$-admissible sequence $(m'_i, a'_i)_{0 \le i \le k'}$ have the
same properties, then $k' = k$ and $(m'_i, a'_i) = (m_i, a_i)$ for every $i \le k$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Theorem 3.2 (Dumont and Thomas, Theorem 1.5). -/
public theorem dumontThomas_numeration {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (a : A) (u : ℕ → A)
    (hfix : ∀ n i (hi : i < (morphExtend η ((List.range n).map u)).length),
      (morphExtend η ((List.range n).map u))[i] = u i)
    (hu₀ : u 0 = a)
    (hgrow : Filter.Tendsto (fun k => (morphIterate η k [a]).length) Filter.atTop
      Filter.atTop)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ k s, (IsLetterAdmissibleSequence η a s k ∧ (s k).1 ≠ [] ∧
        (List.range n).map u =
          ((List.range (k + 1)).reverse.map fun j => morphIterate η j (s j).1).flatten) ∧
      ∀ k' s', (IsLetterAdmissibleSequence η a s' k' ∧ (s' k').1 ≠ [] ∧
        (List.range n).map u =
          ((List.range (k' + 1)).reverse.map fun j => morphIterate η j (s' j).1).flatten) →
        k' = k ∧ ∀ i ≤ k, s' i = s i := by
  -- Every seed iterate is the prefix of the fixed point of its own length.
  have hfirst : (List.range 1).map u = [a] := by simpa using congrArg (fun c => [c]) hu₀
  have hword (k : ℕ) : morphIterate η k [a] =
      (List.range (morphIterate η k [a]).length).map u := by
    induction k with
    | zero => exact hfirst.symm
    | succ k ih =>
      have h := congrArg (morphExtend η) ih
      change morphIterate η (k + 1) [a] = _ at h
      rw [h]
      apply List.ext_getElem (by simp)
      intro i hi _
      simpa only [List.getElem_map, List.getElem_range] using hfix _ i hi
  have hprefix {l m : ℕ} (h : l ≤ m) : (List.range l).map u <+: (List.range m).map u :=
    List.prefix_iff_getElem.mpr ⟨by simpa using h, fun _ _ => by simp⟩
  have hsingle : morphIterate η 1 [a] = η a := by simp [morphIterate, morphExtend]
  have hseed : [a] <+: η a := by
    have hpos : 1 ≤ (morphIterate η 1 [a]).length := by
      rw [hsingle]
      exact List.length_pos_iff.mpr (hη.isNonErasing a)
    calc
      [a] = (List.range 1).map u := hfirst.symm
      _ <+: (List.range (morphIterate η 1 [a]).length).map u := hprefix hpos
      _ = η a := (hword 1).symm.trans hsingle
  have hmono : Monotone (fun j => (morphIterate η j [a]).length) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [iterate_succ_right, List.flatMap_singleton]
    exact (iterate_prefix hseed η k).length_le
  obtain ⟨k, _, hle, hlt⟩ :=
    hgrow.exists_le_lt_succ (show (morphIterate η 0 [a]).length ≤ n from hn)
  -- Split off a top pair at each level of the iterated proper prefix.
  have expand (p : ℕ) (b : A) (m : List A) (hm : m <+: morphIterate η p [b])
      (hmlt : m.length < (morphIterate η p [b]).length) :
      ∃ s : ℕ → List A × A, (0 < p → IsLetterAdmissibleSequence η b s (p - 1)) ∧
        m = ((List.range p).reverse.map fun j => morphIterate η j (s j).1).flatten := by
    induction p generalizing b m with
    | zero =>
      have hmnil : m = [] := List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hmlt)
      exact ⟨fun _ => ([], b), by simp [hmnil]⟩
    | succ p ih =>
      obtain ⟨pre, c, rest, hpre, hrest, hrestlt, heq⟩ :=
        properPrefix_morphIterate_decomposition η hη (p + 1) (by omega) b m hm hmlt
      simp only [Nat.add_one_sub_one] at hrest hrestlt heq ⊢
      obtain ⟨s, hs, hseq⟩ := ih c rest hrest hrestlt
      let t := Function.update s p (pre, c)
      have ht : t p = (pre, c) := Function.update_self ..
      have htlt (i : ℕ) (hi : i < p) : t i = s i := Function.update_of_ne hi.ne ..
      refine ⟨t, fun _ => ⟨?_, by simpa only [ht] using hpre⟩, ?_⟩
      · intro i hi
        have htail := hs (by omega : 0 < p)
        rw [htlt i hi]
        by_cases hip : i + 1 = p
        · rw [hip, ht]
          have hi' : i = p - 1 := by omega
          simpa only [hi'] using htail.2
        · rw [htlt (i + 1) (by omega)]
          exact htail.1 i (by omega)
      · rw [List.range_succ, List.reverse_append]
        simp only [List.reverse_singleton, List.singleton_append, List.map_cons,
          List.flatten_cons, ht]
        rw [heq, hseq]
        congr 2
        apply List.map_congr_left
        intro i hi
        rw [htlt i (by simpa using hi)]
  have hm : (List.range n).map u <+: morphIterate η (k + 1) [a] := by
    rw [hword (k + 1)]
    exact hprefix hlt.le
  obtain ⟨s, hs, hrep⟩ := expand (k + 1) a _ hm (by simpa using hlt)
  have hadm : IsLetterAdmissibleSequence η a s k := hs (by omega)
  have weight {p : ℕ} {t : ℕ → List A × A}
      (ht : (List.range n).map u =
        ((List.range p).reverse.map fun j => morphIterate η j (t j).1).flatten) :
      n = ∑ j ∈ Finset.range p, (morphIterate η j (t j).1).length := by
    have hw := congrArg List.length ht
    rw [List.length_map, List.length_range, List.length_flatten, List.map_map,
      List.map_reverse, List.sum_reverse_nat, ← List.sum_toFinset _ List.nodup_range] at hw
    convert hw using 1
    congr 1
    ext j
    simp
  have hw := weight hrep
  have htop : (s k).1 ≠ [] := by
    intro hempty
    have hp : [(s k).2] <+: η a := by simpa only [hempty, List.nil_append] using hadm.2
    have hc := List.prefix_of_prefix_length_le hp hseed (by simp)
    have hletter := (List.cons_prefix_cons.mp hc).1
    have hbound := admissibleSequence_weightedLength_lt η hη s k hadm.1
    rw [hempty, List.nil_append, hletter, ← hw] at hbound
    exact hbound.not_ge hle
  refine ⟨k, s, ⟨hadm, htop, hrep⟩, ?_⟩
  -- A competing expansion must put n in the same half-open interval of seed lengths.
  intro k' s' ⟨hs', htop', hrep'⟩
  have hw' := weight hrep'
  have hpre' : (s' k').1 <+: η a := (List.prefix_append _ _).trans hs'.2
  have hlead' : [a] <+: (s' k').1 :=
    List.prefix_of_prefix_length_le hseed hpre' (List.length_pos_iff.mpr htop')
  have hle' : (morphIterate η k' [a]).length ≤ n := by
    have hlen := (iterate_prefix hlead' η k').length_le
    rw [hw', Finset.sum_range_succ]
    omega
  have hlt' : n < (morphIterate η (k' + 1) [a]).length := by
    rw [hw', iterate_succ_right, List.flatMap_singleton]
    exact (admissibleSequence_weightedLength_lt η hη s' k' hs'.1).trans_le
      (iterate_prefix hs'.2 η k').length_le
  have hk : k' = k := by
    apply le_antisymm
    · exact le_of_not_gt fun h => hlt.not_ge ((hmono (Nat.succ_le_of_lt h)).trans hle')
    · exact le_of_not_gt fun h => hlt'.not_ge ((hmono (Nat.succ_le_of_lt h)).trans hle)
  subst k'
  exact ⟨rfl, letterAdmissibleSequence_eq_of_weightedLength_eq η hη k a s' s hs' hadm
    (hw'.symm.trans hw)⟩

end MetaMathlibExt
