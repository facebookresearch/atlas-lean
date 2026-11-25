/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PerfectoidSiteComparison

/-!
# Normalized affine-perfectoid v-descent requests

The affine basis has actual complete uniform Tate rings, plus rings,
all-rank continuous valuations and bounded ring maps. Rational and
pro-etale models use their source universal properties. Completed local
adic restrictions and global gluing are integration inputs, not new
requests in this module.

Scholze, *Etale cohomology of diamonds*, arXiv:1709.07343v4:
Theorem 8.7, p43, proves the structural presheaves and representables
are v-sheaves; Proposition 11.9, p56, gives v-descent for diamonds.
The last request is its canonical identity-site quotient comparison.
No arbitrary equivalence or uncharacterized sheaf map is supplied.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PerfectoidVDescent

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels
open MathlibExt.AlgebraicGeometry.PerfectoidSiteComparison

/-- Let $p$ be a prime and $P$ an affinoid perfectoid of characteristic $p$ (`Affine p`). Then the
presheaf represented by $P$ on affinoid perfectoids of characteristic $p$ is a sheaf for the
v-topology. -/
public theorem_wanted affineRepresentableIsVSheaf
    (p : ℕ) [Fact p.Prime] (P : Affine p) :
    Presheaf.IsSheaf (topology p) (yoneda.obj P ⋙ liftTypes)

/-- For a prime $p$, the structure presheaf $(R, R^+) \mapsto R$ on affinoid perfectoids of
characteristic $p$ is a sheaf for the v-topology. -/
public theorem_wanted structurePresheafIsVSheaf
    (p : ℕ) [Fact p.Prime] :
    Presheaf.IsSheaf (topology p) (structurePresheaf p)

/-- For a prime $p$, the integral structure presheaf $(R, R^+) \mapsto R^+$ on affinoid perfectoids
of characteristic $p$ is a sheaf for the v-topology. -/
public theorem_wanted integralPresheafIsVSheaf
    (p : ℕ) [Fact p.Prime] :
    Presheaf.IsSheaf (topology p) (integralPresheaf p)

/-- Let $p$ be a prime and $R \rightrightarrows X$ a representable pro-étale equivalence relation of
perfectoid spaces of characteristic $p$ (`Relation p`). Then the canonical map from the quotient of
$X$ by $R$ in pro-étale sheaves to the v-sheaf quotient, regarded as a pro-étale sheaf, is an
isomorphism. -/
public theorem_wanted quotientComparisonIsIso
    (p : ℕ) [Fact p.Prime] (R : Relation p) :
    IsIso (quotientComparison p R)

end WantedExt.AlgebraicGeometry.PerfectoidVDescent
