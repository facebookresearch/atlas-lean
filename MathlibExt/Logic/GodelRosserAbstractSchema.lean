/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Abstract Gödel-Rosser incompleteness schema

This file derives a true undecidable closed sentence from abstract proof coding,
Rosser representability, consistency, and a diagonal fixed-point interface.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem rosser_rProvable_implies_provable
    {Sentence : Type} {neg : Sentence → Sentence}
    {Provable RProvable : Sentence → Prop} {Proof : Sentence → ℕ → Prop}
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    {s : Sentence} (hs : RProvable s) : Provable s := by
  obtain ⟨n, hn, _⟩ := (hRProof s).mp hs
  exact (hProof s).mpr ⟨n, hn⟩

private theorem rosser_not_provable
    {Sentence : Type} {neg : Sentence → Sentence} {imp : Sentence → Sentence → Sentence}
    {subst : Sentence → ℕ → Sentence} {Provable RProvable : Sentence → Prop}
    {Proof : Sentence → ℕ → Prop} {rPr : Sentence} {code : Sentence → ℕ}
    (hMp : ∀ A B, Provable (imp A B) → Provable A → Provable B)
    (hConsistent : ∀ A, Provable A → Provable (neg A) → False)
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    (hRProvableComplete : ∀ s, RProvable s → Provable (subst rPr (code s)))
    {G : Sentence} (hDiagonalForward : Provable (imp G (neg (subst rPr (code G))))) :
    ¬ Provable G := by
  intro hG
  obtain ⟨n, hn⟩ := (hProof G).mp hG
  have hNoShortRefutation : ∀ m, m < n → ¬ Proof (neg G) m := by
    intro m _ hm
    have hnegG : Provable (neg G) := (hProof (neg G)).mpr ⟨m, hm⟩
    exact hConsistent G hG hnegG
  have hRG : RProvable G :=
    (hRProof G).mpr ⟨n, hn, hNoShortRefutation⟩
  have hRPr : Provable (subst rPr (code G)) := hRProvableComplete G hRG
  have hnotRPr : Provable (neg (subst rPr (code G))) :=
    hMp G (neg (subst rPr (code G))) hDiagonalForward hG
  exact hConsistent (subst rPr (code G)) hRPr hnotRPr

private theorem rosser_not_refutable
    {Sentence : Type} {neg : Sentence → Sentence} {imp : Sentence → Sentence → Sentence}
    {subst : Sentence → ℕ → Sentence} {Provable : Sentence → Prop}
    {rPr : Sentence} {code : Sentence → ℕ}
    (hMp : ∀ A B, Provable (imp A B) → Provable A → Provable B)
    (hConsistent : ∀ A, Provable A → Provable (neg A) → False)
    (hRefutationTransfer : ∀ s, Provable (neg s) → Provable (neg (subst rPr (code s))))
    {G : Sentence}
    (hDiagonalBackward : Provable (imp (neg (subst rPr (code G))) G)) :
    ¬ Provable (neg G) := by
  intro hnegG
  have hnegRPr : Provable (neg (subst rPr (code G))) :=
    hRefutationTransfer G hnegG
  have hG : Provable G :=
    hMp (neg (subst rPr (code G))) G hDiagonalBackward hnegRPr
  exact hConsistent G hG hnegG

private theorem rosser_true
    {Sentence : Type} {neg : Sentence → Sentence} {subst : Sentence → ℕ → Sentence}
    {Provable RProvable TrueInN : Sentence → Prop} {Proof : Sentence → ℕ → Prop}
    {rPr : Sentence} {code : Sentence → ℕ}
    (hTrueNeg : ∀ A, TrueInN (neg A) ↔ ¬ TrueInN A)
    (hProof : ∀ s, Provable s ↔ ∃ n, Proof s n)
    (hRProof : ∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m)
    (hRPrTruth : ∀ s, TrueInN (subst rPr (code s)) ↔ RProvable s)
    {G : Sentence}
    (hDiagonalTruth : TrueInN G ↔ TrueInN (neg (subst rPr (code G))))
    (hNotProvable : ¬ Provable G) : TrueInN G := by
  have hNotRProvable : ¬ RProvable G := by
    intro hRG
    exact hNotProvable (rosser_rProvable_implies_provable hProof hRProof hRG)
  have hNotRPrTrue : ¬ TrueInN (subst rPr (code G)) := by
    intro hRPrTrue
    exact hNotRProvable ((hRPrTruth G).mp hRPrTrue)
  have hNegRPrTrue : TrueInN (neg (subst rPr (code G))) :=
    (hTrueNeg (subst rPr (code G))).mpr hNotRPrTrue
  exact hDiagonalTruth.mpr hNegRPrTrue

/-- **Abstract Gödel–Rosser incompleteness theorem.** Let $\mathcal{L}$ be a set of formulas with
operations $\neg$ and $\to$, a substitution map sending $A \in \mathcal{L}$ and $n \in \mathbb{N}$
to $A[n] \in \mathcal{L}$, a coding map $\ulcorner \cdot \urcorner : \mathcal{L} \to \mathbb{N}$,
a formula $R \in \mathcal{L}$, predicates "provable" (written $\vdash A$), "Rosser provable" and
"true" on $\mathcal{L}$, and a proof relation $\mathrm{Prf}(A, n)$ between formulas $A$ and
natural numbers $n$. Assume that, for all formulas $A$, $B$ and all $n$:
(i) $\neg A$ is true if and only if $A$ is not true;
(ii) if $\vdash A \to B$ and $\vdash A$, then $\vdash B$;
(iii) $\vdash A$ and $\vdash \neg A$ do not both hold;
(iv) $(\neg A)[n] = \neg (A[n])$;
(v) $\vdash A$ if and only if $\mathrm{Prf}(A, k)$ for some $k$;
(vi) $A$ is Rosser provable if and only if there is $k$ with $\mathrm{Prf}(A, k)$ and there is no
$m < k$ with $\mathrm{Prf}(\neg A, m)$;
(vii) $R[\ulcorner A \urcorner]$ is true if and only if $A$ is Rosser provable;
(viii) if $A$ is Rosser provable, then $\vdash R[\ulcorner A \urcorner]$;
(ix) if $\vdash \neg A$, then $\vdash \neg R[\ulcorner A \urcorner]$;
(x) for every formula $F$ there is a formula $G$ with $G[k] = G$ for all $k$,
$\vdash G \to F[\ulcorner G \urcorner]$ and $\vdash F[\ulcorner G \urcorner] \to G$, such that
$G$ is true if and only if $F[\ulcorner G \urcorner]$ is true.
Then there is a formula $G$ with $G[k] = G$ for all $k$ such that $G$ is true, $\nvdash G$ and
$\nvdash \neg G$.

These hypotheses are assumed as an interface; they are not derived from a concrete effective
arithmetic syntax.

Proves `Wanted` entry `godel_rosser_abstract_schema`.

Proof: Apply diagonalization to the negation of the Rosser provability formula, then use
consistency and representability as in Rosser (1936) and Smith, 2nd ed., Chapter 25.

Sources: Kurt Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und
verwandter Systeme I*, Monatshefte für Mathematik und Physik 38 (1931), 173–198;
J. Barkley Rosser, *Extensions of some theorems of Gödel and Church*, Journal of
Symbolic Logic 1 (1936), 87–91.
-/
theorem godel_rosser_abstract_schema :
    ∀ (Sentence : Type)
      (neg : Sentence → Sentence) (imp : Sentence → Sentence → Sentence)
      (subst : Sentence → ℕ → Sentence)
      (Provable RProvable TrueInN : Sentence → Prop)
      (Proof : Sentence → ℕ → Prop) (rPr : Sentence) (code : Sentence → ℕ),
      (∀ G, TrueInN (neg G) ↔ ¬ TrueInN G) →
      (∀ A B, Provable (imp A B) → Provable A → Provable B) →
      (∀ A, Provable A → Provable (neg A) → False) →
      (∀ A n, subst (neg A) n = neg (subst A n)) →
      (∀ s, Provable s ↔ ∃ n, Proof s n) →
      (∀ s, RProvable s ↔ ∃ n, Proof s n ∧ ∀ m, m < n → ¬ Proof (neg s) m) →
      (∀ s, TrueInN (subst rPr (code s)) ↔ RProvable s) →
      (∀ s, RProvable s → Provable (subst rPr (code s))) →
      (∀ s, Provable (neg s) → Provable (neg (subst rPr (code s)))) →
      (∀ F, ∃ G, (∀ n, subst G n = G) ∧
        Provable (imp G (subst F (code G))) ∧
        Provable (imp (subst F (code G)) G) ∧
        (TrueInN G ↔ TrueInN (subst F (code G)))) →
      ∃ G : Sentence, (∀ n, subst G n = G) ∧
        TrueInN G ∧ ¬ Provable G ∧ ¬ Provable (neg G) := by
  intro Sentence neg imp subst Provable RProvable TrueInN Proof rPr code hTrueNeg hMp
    hConsistent hSubstNeg hProof hRProof hRPrTruth hRProvableComplete hRefutationTransfer
    hDiagonal
  obtain ⟨G, hClosed, hDiagonalForward, hDiagonalBackward, hDiagonalTruth⟩ :=
    hDiagonal (neg rPr)
  rw [hSubstNeg rPr (code G)] at hDiagonalForward hDiagonalBackward hDiagonalTruth
  have hNotProvable : ¬ Provable G :=
    rosser_not_provable hMp hConsistent hProof hRProof hRProvableComplete hDiagonalForward
  have hNotRefutable : ¬ Provable (neg G) :=
    rosser_not_refutable hMp hConsistent hRefutationTransfer hDiagonalBackward
  have hTrue : TrueInN G :=
    rosser_true hTrueNeg hProof hRProof hRPrTruth hDiagonalTruth hNotProvable
  exact ⟨G, hClosed, hTrue, hNotProvable, hNotRefutable⟩

end

end MetaMathlibExt
