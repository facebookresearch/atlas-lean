/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.DumontThomasNumeration
import all MathlibExt.Combinatorics.Words.DumontThomasNumeration

/-!
# Proper prefixes in Dumont–Thomas numeration

A proper prefix of an iterated image ends before the end of one of the iterated letter images.

## References

* Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*,
  INTEGERS 24 (2024), Article A112, pp. 1–27, Lemma 3.5 (p. 7).
* Jean-Marie Dumont and Alain Thomas, *Systèmes de numération et fonctions fractales relatifs
  aux substitutions*, Theoretical Computer Science 65 (2) (1989), pp. 153–169, Lemma 1.4.
-/

namespace MetaMathlibExt

open morphIterate_getElem_eq_substitutionAutomaton_tail

-- The decomposition works even for erasing morphisms. Keep the substitution hypothesis
-- of the published statement.
set_option linter.unusedVariables false in
/-- **Decomposition of a proper prefix of an iterated image.** Let $\eta$ be a substitution on
an alphabet $A$, let $\ell \ge 1$ and $a \in A$, and let $m$ be a proper prefix of
$\eta^\ell(a)$, that is, a prefix of strictly smaller length. Then there are words $m'$ and
$m''$ over $A$ and a letter $a' \in A$ such that $m'a'$ is a prefix of $\eta(a)$, $m''$ is a
proper prefix of $\eta^{\ell-1}(a')$, and $m = \eta^{\ell-1}(m')\,m''$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.5 (Dumont and Thomas, Lemma 1.4). -/
public theorem properPrefix_morphIterate_decomposition {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : A) (m : List A)
    (hm : m <+: morphIterate η ℓ [a]) (hlt : m.length < (morphIterate η ℓ [a]).length) :
    ∃ (m' : List A) (a' : A) (m'' : List A), m' ++ [a'] <+: η a ∧
      m'' <+: morphIterate η (ℓ - 1) [a'] ∧
      m''.length < (morphIterate η (ℓ - 1) [a']).length ∧
      m = morphIterate η (ℓ - 1) m' ++ m'' := by
  have hnil (n : ℕ) : morphIterate η n [] = [] :=
    List.append_right_eq_self.mp (iterate_append η n [] []).symm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  have hsplit : morphExtend η [a] = η a ++ [] := by simp [morphExtend]
  have hstep : morphIterate η (n + 1) [a] = morphIterate η n (η a) := by
    simpa only [hnil, List.append_nil] using iterate_split η hsplit n
  rw [hstep] at hm hlt
  simp only [Nat.succ_sub_one]
  generalize η a = w at hm hlt ⊢
  induction w generalizing m with
  | nil => simp [hnil] at hlt
  | cons b w ih =>
    have hcons : morphIterate η n (b :: w) =
        morphIterate η n [b] ++ morphIterate η n w := iterate_append η n [b] w
    rw [hcons] at hm hlt
    have hfirst := List.prefix_append (morphIterate η n [b]) (morphIterate η n w)
    by_cases hin : m.length < (morphIterate η n [b]).length
    · exact ⟨[], b, m, ⟨w, rfl⟩, List.prefix_of_prefix_length_le hm hfirst hin.le,
        hin, by simp [hnil]⟩
    · obtain ⟨tail, rfl⟩ := List.prefix_of_prefix_length_le hfirst hm (Nat.le_of_not_gt hin)
      have htail := (List.prefix_append_right_inj _).mp hm
      simp only [List.length_append, Nat.add_lt_add_iff_left] at hlt
      obtain ⟨pre, b', rest, hp, hr, hlen, heq⟩ := ih tail htail hlt
      refine ⟨b :: pre, b', rest, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, hr, hlen, ?_⟩
      change _ = morphIterate η n ([b] ++ pre) ++ rest
      rw [iterate_append, List.append_assoc, heq]

end MetaMathlibExt
