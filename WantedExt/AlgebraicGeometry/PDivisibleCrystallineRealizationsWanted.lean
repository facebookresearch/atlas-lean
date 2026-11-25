/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

/-!
# Crystal properties of the original covariant Ext module

This request supplies the finite-projective crystal and comparison
with native internal Ext. The coefficient module and its scalar
multiplication are already fixed by actual slice Ext/sheafification.
Source: Scholze--Weinstein1211.6357v2, Sections3.2/4.1; BBM82.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

open _root_.AlgebraicGeometry _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests
open MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

/-- **The covariant Dieudonné module of a $p$-divisible group is a crystal.** Let $p$ be a prime,
$R$ a commutative ring, $G$ a $p$-divisible group over $R$ with a Cartier dual tower $D$ (a
$p$-divisible group whose levels are the Cartier duals of those of $G$), and
$f : \operatorname{Spec} R \to \operatorname{Spec}(A/I)$ a map to the reduction of a PD base
$(A, I)$. Then the covariant module of $G$ on the crystalline site of $\operatorname{Spec} R$ over
$A$, the sheafified $\mathcal{E}xt^1$ of $D$ by the structure sheaf (`covariantModule`), is a
crystal of finite projective modules, and its underlying sheaf is isomorphic to the internal
crystalline $\mathcal{E}xt^1(D, \mathcal{O})$ (`Realization`). -/
public def_wanted covariantDieudonneRealization
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
    (A : PDBase) (f : Spec (.of R) ⟶ A.reduction) : Realization p R G D A f

end WantedExt.AlgebraicGeometry.PDivisibleCrystallineRealizations
