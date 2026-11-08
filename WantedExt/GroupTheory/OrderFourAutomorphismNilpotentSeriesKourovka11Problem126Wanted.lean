/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphisms of order four with few fixed points (Kourovka Notebook Problem 11.126)

Kourovka Notebook, Archive of Solved Problems, Problem 11.126 (P. V. Shumyatskiĭ): are there a
constant `h` and a function `f` such that every finite soluble group `G` with an automorphism `φ` of
order 4 and `|C_G(φ)| ≤ m` has a normal series `1 ≤ M ≤ N ≤ G` with `|G : N| ≤ f(m)`, `N / M`
nilpotent of class at most 2 and `M` nilpotent of class at most `h`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.OrderFourAutomorphismNilpotentSeriesKourovka11Problem126Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.126 (P. V.
Shumyatskiĭ). UnsolvedMath record UM-00700818 (`KOU-11.126`), dataset ulamai/UnsolvedMath v1.8.0.

A normal series means `M` and `N` are normal in `G`. `N / M` nilpotent of class at most 2 is `[[N,
N], N] ≤ M`; `M` nilpotent of class at most `h` is `γ_{h+1}(M) = 1`, written with Mathlib's
`Subgroup.lowerCentralSeries` (index `h` is `γ_{h+1}`). `C_G(φ)` is the fixed-point set of `φ`;
order 4 is `orderOf φ = 4` in `MulAut G`.
-/

/-- Kourovka 11.126 (P. V. Shumyatskiĭ): there are a constant `h` and a function `f` such that if a
finite soluble group `G` has an automorphism `φ` of order 4 with `|C_G(φ)| ≤ m`, then `G` has a
normal series `1 ≤ M ≤ N ≤ G` with `|G : N| ≤ f m`, `N / M` nilpotent of class at most 2 (that is,
`[[N, N], N] ≤ M`) and `M` nilpotent of class at most `h` (`M.lowerCentralSeries h`, the term
`γ_{h+1}(M)` computed in `G`, is trivial). -/
def orderFourAutomorphismBoundedSeries : Prop :=
  ∃ (h : ℕ) (f : ℕ → ℕ), ∀ (m : ℕ) (G : Type) [Group G] [Finite G], Group.IsSolvable G →
    ∀ φ : MulAut G, orderOf φ = 4 → Nat.card {x : G // φ x = x} ≤ m →
      ∃ M N : Subgroup G, M.Normal ∧ N.Normal ∧ M ≤ N ∧ N.index ≤ f m ∧
        ⁅⁅N, N⁆, N⁆ ≤ M ∧ M.lowerCentralSeries h = ⊥

/--
Resolved true: the Kourovka Archive answers 11.126 "Yes, there do" (Makarenko and Khukhro): a finite
soluble group with an automorphism of order 4 having at most `m` fixed points has normal subgroups
`M ≤ N` with `|G : N|` bounded in terms of `m`, `N / M` nilpotent of class at most 2 and `M`
nilpotent of class bounded by an absolute constant. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 11.126 (P. V. Shumyatskiĭ); resolution: N. Yu. Makarenko and E.
I. Khukhro, Algebra and Logic 45 (2006), 326-343, Kourovka Archive, Problem 11.126: "Yes, there do",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted orderFourAutomorphismBoundedSeries_holds : orderFourAutomorphismBoundedSeries

end MathlibExt.GroupTheory.OrderFourAutomorphismNilpotentSeriesKourovka11Problem126Wanted
