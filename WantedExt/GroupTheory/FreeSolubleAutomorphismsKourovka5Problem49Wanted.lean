/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphisms of free soluble groups (Kourovka Notebook Problem 5.49)

Kourovka Notebook, Archive of Solved Problems, Problem 5.49 (V. N. Remeslennikov): let A_(m,n) be
the group of all automorphisms of the free soluble group of derived length n and rank m; is it true
that a) A_(m,n) is finitely generated for any m and n? b) every automorphism in A_(m,n) is induced
by some automorphism in A_(m,n+1)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import WantedExt.GroupTheory.FreeSolubleNormalClosureConjugacyKourovka1Problem89Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.FreeSolubleAutomorphismsKourovka5Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.49 (V. N.
Remeslennikov). UnsolvedMath record UM-00700330 (`KOU-5.49`), dataset ulamai/UnsolvedMath v1.8.0.

The free soluble group of rank `m` and derived length `n` is `F_m / F_m^(n)` for the free group `F_m
= FreeGroup (Fin m)`: `FreeSolubleGroup m n` of the Kourovka 1.89 entry, reused here. An
automorphism `ψ` of `F_m / F_m^(n+1)` induces an automorphism of `F_m / F_m^(n)` (the image of
`F_m^(n)` is fully invariant); the induced map sends `u F^(n)` to `v F^(n)` whenever `ψ` sends `u
F^(n+1)` to `v F^(n+1)`. Both parts are refuted; the targets state the claims for all `m` and `n`.
-/

open MathlibExt.GroupTheory.FreeSolubleNormalClosureConjugacyKourovka1Problem89Wanted
  (FreeSolubleGroup)

/-- Kourovka 5.49(a) (V. N. Remeslennikov): the automorphism group `A_(m,n)` of the free soluble
group of rank `m` and derived length `n` is finitely generated, for all `m` and `n`. -/
def freeSolubleAutomorphismGroupsFG : Prop :=
  ∀ m n : ℕ, Group.FG (MulAut (FreeSolubleGroup m n))

/-- Kourovka 5.49(b) (V. N. Remeslennikov): every automorphism of `F_m / F_m^(n)` is induced by an
automorphism `ψ` of `F_m / F_m^(n+1)`: whenever `ψ` maps `u F^(n+1)` to `v F^(n+1)`, the given
automorphism maps `u F^(n)` to `v F^(n)`. -/
def freeSolubleAutomorphismsLift : Prop :=
  ∀ (m n : ℕ) (φ : MulAut (FreeSolubleGroup m n)), ∃ ψ : MulAut (FreeSolubleGroup m (n + 1)),
    ∀ u v : FreeGroup (Fin m), ψ (QuotientGroup.mk u) = QuotientGroup.mk v →
      φ (QuotientGroup.mk u) = QuotientGroup.mk v

/--
Resolved false: the Kourovka Archive answers 5.49(a) "No": the automorphism group `A_(3,2)` of the
free metabelian group of rank `3` is not finitely generated (Bachmuth and Mochizuki, The nonfinite
generation of Aut(G), G free metabelian of rank 3, Trans. Amer. Math. Soc. 270 (1982)), although
`A_(m,2)` is finitely generated for `m ≠ 3`. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 5.49 (V. N. Remeslennikov); resolution: (a) S. Bachmuth and H.
Y. Mochizuki, The nonfinite generation of Aut(G), G free metabelian of rank 3, Trans. Amer. Math.
Soc. 270 (1982), 693-700, and Aut(F) → Aut(F/F'') is surjective for free group F of rank ≥ 4, Trans.
Amer. Math. Soc. 292 (1985), 81-101; (b) V. Shpilrain, Automorphisms of F/R' groups, Internat. J.
Algebra Comput. 1 (1991), 177-184, Kourovka Archive, Problem 5.49: a) No: A_(3,2) is not finitely
generated, although A_(m,2) is whenever m ≠ 3 (Bachmuth-Mochizuki); b) No (Shpilrain),
https://doi.org/10.1090/S0002-9947-1982-0645339-3.
-/
public theorem_wanted freeSolubleAutomorphismGroupsFG_refuted : ¬ freeSolubleAutomorphismGroupsFG

/--
Resolved false: the Kourovka Archive answers 5.49(b) "No", citing Shpilrain, Automorphisms of F/R'
groups (Internat. J. Algebra Comput. 1 (1991), 177-184, https://doi.org/10.1142/S0218196791000109):
some automorphism of a free soluble group `F_m / F_m^(n)` is induced by no automorphism of `F_m /
F_m^(n+1)`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.49
(V. N. Remeslennikov); resolution: (a) S. Bachmuth and H. Y. Mochizuki, The nonfinite generation of
Aut(G), G free metabelian of rank 3, Trans. Amer. Math. Soc. 270 (1982), 693-700, and Aut(F) →
Aut(F/F'') is surjective for free group F of rank ≥ 4, Trans. Amer. Math. Soc. 292 (1985), 81-101;
(b) V. Shpilrain, Automorphisms of F/R' groups, Internat. J. Algebra Comput. 1 (1991), 177-184,
Kourovka Archive, Problem 5.49: a) No: A_(3,2) is not finitely generated, although A_(m,2) is
whenever m ≠ 3 (Bachmuth-Mochizuki); b) No (Shpilrain),
https://doi.org/10.1090/S0002-9947-1982-0645339-3.
-/
public theorem_wanted freeSolubleAutomorphismsLift_refuted : ¬ freeSolubleAutomorphismsLift

end MathlibExt.GroupTheory.FreeSolubleAutomorphismsKourovka5Problem49Wanted
