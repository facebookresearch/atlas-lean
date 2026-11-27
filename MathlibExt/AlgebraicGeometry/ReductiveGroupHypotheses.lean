/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralReductiveSources

/-!
# Group-level reductivity through actual rational representations

Finite rational representations are actual scheme actions on affine
vector spaces, normalized to linear automorphisms on every coefficient
algebra. Linear reductivity means that every invariant subspace has an
invariant complement. For connected affine algebraic groups over C this
is the usual reductive-group hypothesis of the source.

This group hypothesis is distinct from central radical of its Lie
algebra: the additive group has abelian Lie algebra and is not reductive.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Section0.5;
the characteristic-zero equivalence of reductivity and complete
reducibility of rational representations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ReductiveGroupHypotheses

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open SchemeLieJetFamilies

variable {k : Type} [Field k]

def vectorPoint {n : ℕ} (A : CommAlgCat.{0} k) (v : Fin n → A) :
    affine A ⟶ CameralChevalleyModels.space (k := k) (r := n) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) =
        Spec.map (CommRingCat.ofHom (algebraMap k A))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (MvPolynomial.aeval v).commutes x)

variable (G : Over (Spec (.of k))) [GrpObj G]

structure RationalRepresentation (n : ℕ) where
  [action : ModObj G (CameralChevalleyModels.space (k := k) (r := n))]
  linear : ∀ A : CommAlgCat.{0} k, (affine A ⟶ G) → ((Fin n → A) ≃ₗ[A] (Fin n → A))
  normalized : ∀ (A : CommAlgCat.{0} k) (g : affine A ⟶ G) (v : Fin n → A),
    CartesianMonoidalCategory.lift g (vectorPoint A v) ≫
      γ[G,CameralChevalleyModels.space (k := k) (r := n)] =
        vectorPoint A (linear A g v)

def extendedSubspace {n : ℕ} (A : CommAlgCat.{0} k) (P : Submodule k (Fin n → k)) :
    Submodule A (Fin n → A) :=
  Submodule.span A {v | ∃ p : P, v = fun i => algebraMap k A (p.val i)}

def Invariant {n : ℕ} (F : RationalRepresentation G n) (P : Submodule k (Fin n → k)) : Prop :=
  ∀ (A : CommAlgCat.{0} k) (g : affine A ⟶ G) (v : Fin n → A),
    v ∈ extendedSubspace A P → F.linear A g v ∈ extendedSubspace A P

def IsLinearlyReductive : Prop :=
  ∀ (n : ℕ) (F : RationalRepresentation G n) (P : Submodule k (Fin n → k)),
    Invariant G F P → ∃ Q : Submodule k (Fin n → k), IsCompl P Q ∧ Invariant G F Q

end MathlibExt.AlgebraicGeometry.ReductiveGroupHypotheses
