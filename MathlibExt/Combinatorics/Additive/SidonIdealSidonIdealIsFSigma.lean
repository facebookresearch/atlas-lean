/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions
public import MathlibExt.Combinatorics.Additive.SidonIdeal
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The Sidon ideal is `F_σ`

A set lies in the Sidon ideal when it is covered by `n` Sidon sets for some `n`.
Equivalently, its indicator function has a coloring with `n` colors whose
monochromatic quadruples all satisfy the Sidon condition. For fixed `n`, the
space of colorings is compact, and the set of valid indicator-coloring pairs is
closed, since the Sidon condition on one quadruple constrains only finitely many
coordinates. The set of valid indicators is thus the projection of a closed set
along a compact factor, hence closed.
-/

namespace MetaMathlibExt

@[expose] public section

/-- One quadruple imposes a closed condition on indicator-coloring pairs: it only
constrains finitely many coordinates, so it is the preimage of a set in a
discrete space. -/
private theorem SidonIdealFSigma.isClosed_single (n a b d e : ℕ) :
    IsClosed {p : (ℕ → Bool) × (ℕ → Fin n) | p.1 a = true → p.1 b = true →
      p.1 d = true → p.1 e = true → p.2 a = p.2 b → p.2 b = p.2 d →
      p.2 d = p.2 e → a + b = d + e → (a = d ∧ b = e) ∨ (a = e ∧ b = d)} := by
  have hΦ : Continuous (fun p : (ℕ → Bool) × (ℕ → Fin n) =>
      ((p.1 a, p.1 b, p.1 d, p.1 e), (p.2 a, p.2 b, p.2 d, p.2 e))) := by
    refine Continuous.prodMk
      (Continuous.prodMk ((continuous_apply a).comp continuous_fst)
        (Continuous.prodMk ((continuous_apply b).comp continuous_fst)
          (Continuous.prodMk ((continuous_apply d).comp continuous_fst)
            ((continuous_apply e).comp continuous_fst))))
      (Continuous.prodMk ((continuous_apply a).comp continuous_snd)
        (Continuous.prodMk ((continuous_apply b).comp continuous_snd)
          (Continuous.prodMk ((continuous_apply d).comp continuous_snd)
            ((continuous_apply e).comp continuous_snd))))
  have hrfl : {p : (ℕ → Bool) × (ℕ → Fin n) | p.1 a = true → p.1 b = true →
        p.1 d = true → p.1 e = true → p.2 a = p.2 b → p.2 b = p.2 d →
        p.2 d = p.2 e → a + b = d + e → (a = d ∧ b = e) ∨ (a = e ∧ b = d)} =
      (fun p : (ℕ → Bool) × (ℕ → Fin n) =>
        ((p.1 a, p.1 b, p.1 d, p.1 e), (p.2 a, p.2 b, p.2 d, p.2 e))) ⁻¹'
        {v : (Bool × Bool × Bool × Bool) × (Fin n × Fin n × Fin n × Fin n) |
          v.1.1 = true → v.1.2.1 = true → v.1.2.2.1 = true →
          v.1.2.2.2 = true → v.2.1 = v.2.2.1 → v.2.2.1 = v.2.2.2.1 →
          v.2.2.2.1 = v.2.2.2.2 → a + b = d + e →
          (a = d ∧ b = e) ∨ (a = e ∧ b = d)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [hrfl]
  exact (isClosed_discrete _).preimage hΦ

/-- All quadruples jointly impose a closed condition on indicator-coloring
pairs. -/
private theorem SidonIdealFSigma.isClosed_forall (n : ℕ) :
    IsClosed {p : (ℕ → Bool) × (ℕ → Fin n) | ∀ a b d e : ℕ, p.1 a = true →
      p.1 b = true → p.1 d = true → p.1 e = true → p.2 a = p.2 b →
      p.2 b = p.2 d → p.2 d = p.2 e → a + b = d + e →
      (a = d ∧ b = e) ∨ (a = e ∧ b = d)} := by
  have heq : {p : (ℕ → Bool) × (ℕ → Fin n) | ∀ a b d e : ℕ, p.1 a = true →
        p.1 b = true → p.1 d = true → p.1 e = true → p.2 a = p.2 b →
        p.2 b = p.2 d → p.2 d = p.2 e → a + b = d + e →
        (a = d ∧ b = e) ∨ (a = e ∧ b = d)} =
      ⋂ a, ⋂ b, ⋂ d, ⋂ e, {p : (ℕ → Bool) × (ℕ → Fin n) | p.1 a = true →
        p.1 b = true → p.1 d = true → p.1 e = true → p.2 a = p.2 b →
        p.2 b = p.2 d → p.2 d = p.2 e → a + b = d + e →
        (a = d ∧ b = e) ∨ (a = e ∧ b = d)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun d => isClosed_iInter fun e =>
      SidonIdealFSigma.isClosed_single n a b d e

/-- **The Sidon ideal is $F_\sigma$.** Give the Cantor space $\{0, 1\}^{\mathbb{N}}$ the product
topology and identify each set $A \subseteq \mathbb{N}$ with its indicator function. Then the set
of indicator functions of the members of the Sidon ideal is a countable union of closed subsets
of $\{0, 1\}^{\mathbb{N}}$.

Source: Andrzej Nowik, *On the Sidon Ideal*, INTEGERS 25 (2025), Article A91,
Corollary 2 (`integers-2025-A91-cor-2`). -/
public theorem sidonIdeal_isFSigma :
    ∃ F : ℕ → Set (ℕ → Bool), (∀ k, IsClosed (F k)) ∧
      {f : ℕ → Bool | {n | f n = true} ∈ sidonIdeal} = ⋃ k, F k := by
  refine ⟨fun k => Prod.fst '' {p : (ℕ → Bool) × (ℕ → Fin k) | ∀ a b d e : ℕ,
    p.1 a = true → p.1 b = true → p.1 d = true → p.1 e = true → p.2 a = p.2 b →
    p.2 b = p.2 d → p.2 d = p.2 e → a + b = d + e →
    (a = d ∧ b = e) ∨ (a = e ∧ b = d)}, fun k => ?_, ?_⟩
  · exact isClosedMap_fst_of_compactSpace _ (SidonIdealFSigma.isClosed_forall k)
  · ext f
    constructor
    · intro hf
      have hf' : {n | f n = true} ∈ sidonIdeal := hf
      obtain ⟨n, S, hS, hsub⟩ := hf'
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · refine Set.mem_iUnion.2
          ⟨1, (f, fun _ => (⟨0, Nat.one_pos⟩ : Fin 1)), ?_, rfl⟩
        intro a b d e ha hb hd he _ _ _ _
        have haA : a ∈ ({n | f n = true} : Set ℕ) := ha
        obtain ⟨j, -⟩ := Set.mem_iUnion.1 (hsub haA)
        exact j.elim0
      · have hchoice : ∀ x : ℕ, ∃ j : Fin n,
            x ∈ ({n | f n = true} : Set ℕ) → x ∈ S j := by
          intro x
          by_cases hx : x ∈ ({n | f n = true} : Set ℕ)
          · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hsub hx)
            exact ⟨j, fun _ => hj⟩
          · exact ⟨⟨0, hn⟩, fun h => absurd h hx⟩
        choose c hc using hchoice
        refine Set.mem_iUnion.2 ⟨n, (f, c), ?_, rfl⟩
        change ∀ a b d e : ℕ, f a = true → f b = true → f d = true → f e = true →
          c a = c b → c b = c d → c d = c e → a + b = d + e →
          (a = d ∧ b = e) ∨ (a = e ∧ b = d)
        intro a b d e ha hb hd he hab hbc hcd hsum
        have haA : a ∈ ({n | f n = true} : Set ℕ) := ha
        have hbA : b ∈ ({n | f n = true} : Set ℕ) := hb
        have hdA : d ∈ ({n | f n = true} : Set ℕ) := hd
        have heA : e ∈ ({n | f n = true} : Set ℕ) := he
        have ha' : a ∈ S (c a) := hc a haA
        have hb' : b ∈ S (c a) := by rw [hab]; exact hc b hbA
        have hd' : d ∈ S (c a) := by rw [hab, hbc]; exact hc d hdA
        have he' : e ∈ S (c a) := by rw [hab, hbc, hcd]; exact hc e heA
        exact hS (c a) a ha' b hb' d hd' e he' hsum
    · intro hf
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hf
      obtain ⟨p, hp, rfl⟩ := (Set.mem_image _ _ _).1 hk
      change {n | (Prod.fst p) n = true} ∈ sidonIdeal
      refine ⟨k, fun j => {x | p.1 x = true ∧ p.2 x = j}, fun j => ?_, ?_⟩
      · have hp' : ∀ a b d e : ℕ, p.1 a = true → p.1 b = true → p.1 d = true →
          p.1 e = true → p.2 a = p.2 b → p.2 b = p.2 d → p.2 d = p.2 e →
          a + b = d + e → (a = d ∧ b = e) ∨ (a = e ∧ b = d) := hp
        intro a ha b hb d hd e he hsum
        exact hp' a b d e ha.1 hb.1 hd.1 he.1 (ha.2.trans hb.2.symm)
          (hb.2.trans hd.2.symm) (hd.2.trans he.2.symm) hsum
      · intro x hx
        exact Set.mem_iUnion.2 ⟨p.2 x, hx, rfl⟩

end

end MetaMathlibExt
