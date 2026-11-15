/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.CrystallinePrismaticCohomology

/-!
# Prismatic–de Rham comparison over the actual crystalline prism

The source is RΓ of the structural sheaf of the actual δ-lift site over
`(Z_p,(p))`, specialized by the two-term free resolution of `F_p`. The
scalar extension is along the actual prism Frobenius, which is proved to
be the identity on `Z_p`. The target is actual right-derived prime-field
sections of the normalized de Rham complex, restricted along `Z_p → F_p`.

This packet requests the underlying derived-module comparison in this
crystalline-prism scope. Ordinary δ-ring, exterior-power and de Rham
constructors are completed or explicit source-covered inputs. A free
period complex or replacement cohomology module is not an input.

Reference: Bhatt–Scholze, *Prisms and prismatic cohomology*, Theorem
1.8(3); Example 3.3, Lemma 3.5 and Definition 4.1 give the exact objects
and flat topology. The standard crystalline prism has identity Frobenius.
https://arxiv.org/abs/1905.08229
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CrystallinePrismaticComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CrystallinePrismaticSite
open MathlibExt.AlgebraicGeometry.CrystallinePrismaticCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The actual prismatic derived specialization agrees with de Rham. -/
public theorem_wanted prismaticDeRhamComparison
    (p : ℕ) [Fact p.Prime] (X : PrimeFieldScheme p)
    [IsProper X.hom] [Smooth X.hom]
    (D : MathlibExt.AlgebraicGeometry.PrimeFieldDeRham.Differential p X) :
    Nonempty (specialization p X ≅ deRham p X D)

end WantedExt.AlgebraicGeometry.CrystallinePrismaticComparison
