/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionSecondPage
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionTotalAugmentation
public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence

/-!
# The filtration on Hochschild homology from a polynomial resolution

Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` a `k`-flat commutative
algebra. The Hochschild bicomplex of the canonical polynomial resolution of `B` has a
horizontal-total filtration. The total augmentation induces an isomorphism to the Hochschild
homology of `B` with coefficients in itself, and transporting the filtration gives an
`EInt`-indexed filtration of each `HH_n(B/k;B)`.

For `n = p + q`, its graded piece at `p` is the cokernel of the inclusion from stage `p−1` to
stage `p`. Page `r` at `(p,q)` is isomorphic to this graded piece when `r ≥ 1`, `p+1 ≤ r`, and
`q+2 ≤ r`. The filtration is exhaustive at stage `n` in total degree `n`.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k) [Module.Flat k B]

local notation "C" => ModuleCat.{max u v} k
local notation "K" => bicomplex k B

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be flat as a
`k`-module. For `n : ℕ`, the `EInt`-indexed filtration of `(Symmetric.chainComplex k B
B).homology n` is the horizontal-total homology filtration of the polynomial-resolution
bicomplex `bicomplex k B`, transported along `(totalHochschildHomologyIso k B n).hom`. -/
def hochschildHomologyFiltration (n : ℕ) :
    CategoryTheory.Filtration ((Symmetric.chainComplex k B B).homology n) EInt where
  toMonoOver := (HomologicalComplex₂.horizontalTotalHomologyFiltration K n).toMonoOver ⋙
    MonoOver.map (totalHochschildHomologyIso k B n).hom

/-- For a commutative ring `k : Type u`, a `k`-flat algebra `B : CommAlgCat.{max u v} k`, and `p, q : ℕ`, the filtration
inclusion at total degree `p+q` is
`(hochschildHomologyFiltration k B (p+q)).obj (p−1) ⟶ (hochschildHomologyFiltration k B (p+q)).obj p`,
where the indices are the integers `(p : ℤ)−1` and `(p : ℤ)` viewed in `EInt`. It is induced by the order relation `p−1
≤ p`. -/
def hochschildFiltrationStepMap (p q : ℕ) :
    (hochschildHomologyFiltration k B (p + q)).obj (((p : ℤ) - 1 : ℤ) : EInt) ⟶
      (hochschildHomologyFiltration k B (p + q)).obj ((p : ℤ) : EInt) :=
  ((hochschildHomologyFiltration k B (p + q)).toMonoOver.map
    (homOfLE (HomologicalComplex₂.horizontalTotalHomologyPrevIndex_le p))).hom.left

/-- For a commutative ring `k : Type u`, a `k`-flat algebra `B : CommAlgCat.{max u v} k`, and `p,
q : ℕ`, the object `hochschildAssociatedGraded k B p q : ModuleCat.{max u v} k` is the
cokernel of `hochschildFiltrationStepMap k B p q`. It is the quotient of filtration stage `p`
by stage `p−1` in Hochschild homology of total degree `p+q`. -/
abbrev hochschildAssociatedGraded (p q : ℕ) : C :=
  CategoryTheory.Limits.cokernel (hochschildFiltrationStepMap k B p q)

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be `k`-flat. For `p, q : ℕ`,
`hochschildAssociatedGraded k B p q = HomologicalComplex₂.horizontalTotalHomologyGradedPiece (bicomplex k B) p q`.
Transport along the total augmentation changes the ambient homology object while retaining the filtration objects and
the map whose cokernel defines this graded piece. -/
theorem hochschildAssociatedGraded_eq (p q : ℕ) :
    hochschildAssociatedGraded k B p q = HomologicalComplex₂.horizontalTotalHomologyGradedPiece K p q := rfl

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be `k`-flat. For `p, q : ℕ` and `r : ℤ`
satisfying `1 ≤ r`, `(p : ℤ)+1 ≤ r`, and `(q : ℤ)+2 ≤ r`, there is an isomorphism
`((spectralSequence k B).page r).X (p,q) ≅ hochschildAssociatedGraded k B p q`.
The target is the stage-`p` graded quotient of `HH_{p+q}(B/k;B)` under the filtration transported by the total
augmentation. -/
def stablePageHochschildGradedIso (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hp : (p : ℤ) + 1 ≤ r) (hq : (q : ℤ) + 2 ≤ r) :
    ((spectralSequence k B).page r).X (p, q) ≅ hochschildAssociatedGraded k B p q :=
  HomologicalComplex₂.horizontalStablePageGradedIso K r hr p q hp hq ≪≫
    eqToIso (hochschildAssociatedGraded_eq k B p q).symm

/-- For a commutative ring `k : Type u`, a `k`-flat algebra `B : CommAlgCat.{max u v} k`, and `n : ℕ`, the inclusion of
filtration stage `((n : ℤ) : EInt)` into `(Symmetric.chainComplex k B B).homology n` is an isomorphism:
`IsIso ((hochschildHomologyFiltration k B n).ι.app ((n : ℤ) : EInt))`.
Thus stage `n` exhausts Hochschild homology in degree `n`. -/
theorem hochschildHomologyFiltration_exhaustive (n : ℕ) :
    IsIso ((hochschildHomologyFiltration k B n).ι.app ((n : ℤ) : EInt)) := by
  letI : IsIso ((HomologicalComplex₂.horizontalTotalHomologyFiltration K n).ι.app
    ((n : ℤ) : EInt)) := HomologicalComplex₂.horizontalTotalHomologyFiltration_exhaustive K n
  change IsIso ((HomologicalComplex₂.horizontalTotalHomologyFiltration K n).ι.app
    ((n : ℤ) : EInt) ≫ (totalHochschildHomologyIso k B n).hom)
  infer_instance

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
