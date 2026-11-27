/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

/-!
# Finite tensor transition normalization

The evaluation-conjugate transition on finite dual–line tensors sends pure tensors to the
pure tensors of their dual and line transition images.

Source: Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral p-adic Hodge theory*,
BMS19 arXiv:1802.03261v2, Theorem1.12(3), footnote3, Sections5.1/7.3/7.4;
Bhatt–Scholze, *Prisms and Prismatic Cohomology*, arXiv:1905.08229v4, Sections12–15.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry AbsolutePrismaticBasis PrismaticFilteredTwists
open CompletedFilteredPrismaticTensors
open scoped TensorProduct

private lemma zeroTransition {C : Type 1} [Category.{0} C]
    {coeff : ℕ → Cᵒᵖ ⥤ CommRingCat.{0}} {q : ∀ n : ℕ, coeff (n + 1) ⟶ coeff n}
    {J : GrothendieckTopology C} (L : FiniteLineTower coeff q J)
    (n : ℕ) (B : Cᵒᵖ) (r : (coeff (n + 1)).obj B) :
    ((L.transition n 0).app B).hom r = ((q n).app B).hom r := by
  let t : (coeff (n + 1)).obj B → (coeff n).obj B :=
    ((L.transition n 0).app B).hom
  have h : t 1 = 1 := L.positive_word n 0 B (fun i ↦ Fin.elim0 i)
  have hs : t (r * 1) = ((q n).app B).hom r * t 1 :=
    ((L.transition n 0).app B).hom.map_smul r (1 : (coeff (n + 1)).obj B)
  change t r = ((q n).app B).hom r
  simpa only [mul_one, h] using hs

/-- For a prime $p$, a quasisyntomic ring `A` with chosen initial prisms `D` over the semiperfectoid
basis of its site, a zero reduction `Z` and a twist tower `T` (finite filtered Breuil–Kisin lines
$L_n$ and their duals $L_n^\vee$ over the finite quotient coefficient rings): the transition from
level $n + 1$ to level $n$ of the tensor products $L_n^\vee \otimes L_n$, obtained from the
weight-zero transition of `T` through the evaluation isomorphisms, sends every pure tensor
$f \otimes x$ to $f' \otimes x'$, where $f'$ and $x'$ are the images of $f$ and $x$ under the dual
and line transitions. -/
public theorem finiteTensorTransition
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z) :
    TensorTransitionNormalization p A D Z T
    := by
  constructor
  intro n B f x
  let e₀ : (T.data.dual n).obj B ⊗[(quotientPresheaf p A D n).obj B]
      (T.data.line n).obj B → (quotientPresheaf p A D n).obj B :=
    ((T.data.evaluation n).hom.app B).hom
  let e₁ : (T.data.dual (n + 1)).obj B ⊗[(quotientPresheaf p A D (n + 1)).obj B]
      (T.data.line (n + 1)).obj B → (quotientPresheaf p A D (n + 1)).obj B :=
    ((T.data.evaluation (n + 1)).hom.app B).hom
  let v : (quotientPresheaf p A D n).obj B →
      (T.data.dual n).obj B ⊗[(quotientPresheaf p A D n).obj B] (T.data.line n).obj B :=
    ((T.data.evaluation n).inv.app B).hom
  let t : (quotientPresheaf p A D (n + 1)).obj B → (quotientPresheaf p A D n).obj B :=
    ((T.data.transition n 0).app B).hom
  let y := finiteDualStepValue T.data n B f ⊗ₜ[(quotientPresheaf p A D n).obj B]
    finiteLineStepValue T.data n B x
  change ULift.up (v (t (e₁ (f ⊗ₜ[(quotientPresheaf p A D (n + 1)).obj B] x)))) =
    ULift.up y
  apply congrArg ULift.up
  have hs : t (e₁ (f ⊗ₜ[(quotientPresheaf p A D (n + 1)).obj B] x)) =
      ((quotientPresheafTransition p A D n).app B).hom
        (e₁ (f ⊗ₜ[(quotientPresheaf p A D (n + 1)).obj B] x)) :=
    zeroTransition T.data n B _
  have he : e₀ y = ((quotientPresheafTransition p A D n).app B).hom
      (e₁ (f ⊗ₜ[(quotientPresheaf p A D (n + 1)).obj B] x)) :=
    T.data.evaluation_transition n B f x
  rw [hs, ← he]
  have hi := congrArg (fun k ↦ (k.app B).hom y) (T.data.evaluation n).hom_inv_id
  exact hi

end WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
