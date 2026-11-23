/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Loewy series of permutation modules of p-groups (Kourovka Notebook Problem 8.49)

Kourovka Notebook, Archive of Solved Problems, Problem 8.49 (P. M. Neumann): let `G` be a `p`-group
acting transitively as a permutation group on a set `Ω`, let `F` be a field of characteristic `p`,
and regard `FΩ` as an `FG`-module. Then do the descending and ascending Loewy series of `FΩ`
coincide?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Algebra.PermutationModuleLoewySeriesKourovka8Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.49 (P. M.
Neumann). UnsolvedMath record UM-00700499 (`KOU-8.49`), dataset ulamai/UnsolvedMath v1.8.0.

`G` and `Ω` are finite and `FΩ` is realized as `Ω → F` with `g` acting by `(g · m)(ω) = m(g⁻¹ ω)`.
For a finite `p`-group in characteristic `p` the Jacobson radical `J` of `FG` is the augmentation
ideal, spanned by the elements `g - 1`, and for modules over the Artinian ring `FG` the radical of a
module `M` is `J M` and its socle is the annihilator of `J` in `M`. So the descending Loewy series
is `Jᵏ FΩ` (`radicalLayer`) and the ascending one is the annihilators of `Jᵏ` (`socleLayer`). They
coincide when, for the Loewy length `L`, `Jᵏ FΩ = soc^{L - k}(FΩ)` for every `k ≤ L`.
-/

/-- The permutation module `FΩ`, realized as `Ω → F`, with `g` acting by `(g · m)(ω) = m(g⁻¹ ω)`. -/
def permAct {G Ω F : Type*} [Group G] [MulAction G Ω] (g : G) (m : Ω → F) : Ω → F :=
  fun ω => m (g⁻¹ • ω)

/-- The radical series `Jᵏ · FΩ`, where `J` is the augmentation ideal of `FG`, spanned by the
elements `g - 1`: `J⁰ · FΩ = FΩ` and `Jᵏ⁺¹ · FΩ` is spanned by the `g · m - m`, `m ∈ Jᵏ · FΩ`. -/
def radicalLayer (G Ω F : Type*) [Group G] [MulAction G Ω] [Field F] : ℕ → Submodule F (Ω → F)
  | 0 => ⊤
  | k + 1 => Submodule.span F {v | ∃ g : G, ∃ m ∈ radicalLayer G Ω F k, v = permAct g m - m}

/-- The socle series: the elements of `FΩ` annihilated by `Jᵏ`; `soc⁰ = 0` and `m ∈ socᵏ⁺¹`
exactly when `g · m - m ∈ socᵏ` for every `g`. -/
def socleLayer (G Ω F : Type*) [Group G] [MulAction G Ω] [Field F] : ℕ → Submodule F (Ω → F)
  | 0 => ⊥
  | k + 1 =>
    { carrier := {m | ∀ g : G, permAct g m - m ∈ socleLayer G Ω F k}
      add_mem' := fun {a b} ha hb g => by
        have := (socleLayer G Ω F k).add_mem (ha g) (hb g)
        convert this using 1
        funext ω
        simp [permAct]
        ring
      zero_mem' := fun g => by
        convert (socleLayer G Ω F k).zero_mem using 1
        funext ω
        simp [permAct]
      smul_mem' := fun c m hm g => by
        convert (socleLayer G Ω F k).smul_mem c (hm g) using 1
        funext ω
        simp [permAct]
        ring }

/-- Kourovka 8.49 (P. M. Neumann): for a finite `p`-group `G` acting transitively on a finite set
`Ω` and a field `F` of characteristic `p`, the radical (descending Loewy) series and the socle
(ascending Loewy) series of the permutation module `FΩ` coincide: for the Loewy length `L`,
`Jᵏ · FΩ = soc^{L - k}(FΩ)` for every `k ≤ L`. -/
def permutationModuleLoewySeriesCoincide : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∀ (Ω : Type) [MulAction G Ω] [Finite Ω], MulAction.IsPretransitive G Ω →
    ∀ (F : Type) [Field F] [CharP F p], ∃ L : ℕ, radicalLayer G Ω F L = ⊥ ∧
      ∀ k ≤ L, radicalLayer G Ω F k = socleLayer G Ω F (L - k)

/--
Resolved true: the Kourovka Archive answers 8.49 "Yes, they do", citing Alperin, Loewy structure of
permutation modules for p-groups (1988). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 8.49 (P. M. Neumann); resolution: J. L. Alperin, Loewy structure of
permutation modules for p-groups, Quart. J. Math. Oxford (2) 39 (1988), 129-133, Kourovka Archive,
Problem 8.49: Yes, they do (Alperin); paper, main theorem as stated in the zbMATH review Zbl
0657.20004: for a finite p-group P transitive on Ω and any field K of characteristic p, KΩ has
coincident upper and lower Loewy series, https://doi.org/10.1093/qmath/39.2.129.
-/
public theorem_wanted permutationModuleLoewySeriesCoincide_holds :
    permutationModuleLoewySeriesCoincide

end MathlibExt.Algebra.PermutationModuleLoewySeriesKourovka8Problem49Wanted
