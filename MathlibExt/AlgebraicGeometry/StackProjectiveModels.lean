/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackVectorBundles

/-!
# Relative projectivization and projective stack morphisms

The projective point functor is the actual set of invertible module quotients,
modulo quotient-preserving linear isomorphism. Its restriction is fixed by
the scalar-extension universal property and the actual module restriction
map. The represented stack model is an equivalence over the actual affine
stack-point category. Projectivity is a global closed factorization through
this projectivization of a finitely presented cartesian module; it is not
merely pointwise projectivity of unrelated scheme fibres.

Sources: EGA II, relative Proj; Kresch arXiv:math/9810166v1,
Convention 2.1.1. Generic Proj/QCoh representation is completed public
source mathematics, while the native comparison dictionary is explicit.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackProjectiveModels

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules
open StackVectorBundles

def LocalRank (R : CommRingCat.{0}) (M : ModuleCat.{0} R) (r : ℕ) : Prop :=
  ∀ q : PrimeSpectrum R, ∃ f : R, f ∉ q.asIdeal ∧
    Nonempty (Module.Basis (Fin r) (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M))

structure LineQuotient (R : CommRingCat.{0}) (M : ModuleCat.{0} R) where
  line : ModuleCat.{0} R
  rankOne : LocalRank R line 1
  finitePresentation : Module.FinitePresentation R line
  quotient : M ⟶ line
  surjective : Function.Surjective quotient

def QuotientRelated {R : CommRingCat.{0}} {M : ModuleCat.{0} R}
    (q p : LineQuotient R M) : Prop :=
  ∃ e : q.line ≅ p.line, q.quotient ≫ e.hom = p.quotient

def quotientSetoid (R : CommRingCat.{0}) (M : ModuleCat.{0} R) :
    Setoid (LineQuotient R M) where
  r := QuotientRelated
  iseqv :=
    { refl := fun q => ⟨Iso.refl _, by simp⟩
      symm := by
        intro q p h
        obtain ⟨e, he⟩ := h
        exact ⟨e.symm, by rw [← he]; simp⟩
      trans := by
        intro q p t h k
        obtain ⟨e, he⟩ := h
        obtain ⟨i, hi⟩ := k
        exact ⟨e.trans i, by simp only [Iso.trans_hom, ← Category.assoc, he, hi]⟩ }

abbrev QuotientSet (R : CommRingCat.{0}) (M : ModuleCat.{0} R) :=
  Quotient (quotientSetoid R M)

/-- The quotient pullback is actual scalar extension, with its quotient
map square fixed by the given semilinear restriction. -/
def IsQuotientPullback {R B : CommRingCat.{0}} {M : ModuleCat.{0} R}
    {N : ModuleCat.{0} B} (f : R →+* B) (u : M →ₛₗ[f] N)
    (q : LineQuotient R M) (p : LineQuotient B N) : Prop :=
  ∃ v : q.line →ₛₗ[f] p.line,
    (∀ Q : ModuleCat.{0} B, Function.Bijective
      (fun g : p.line →ₗ[B] Q => g.comp v)) ∧
    v.comp q.quotient.hom = p.quotient.hom.comp u

variable {S : Scheme.{0}}

abbrev QuotientAt {X : Stack S} (M : FPModule X) (a : (AffinePoint X)ᵒᵖ) :=
  LineQuotient ((rings X).obj a) (M.presheaf.obj a)

/-- A model of the fixed quotient functor. Objects are literally quotient
classes, and every restriction is prescribed by the tensor universal property. -/
structure ProjectivePresheaf {X : Stack S} (M : FPModule X) where
  functor : (AffinePoint X)ᵒᵖ ⥤ Type 1
  object_eq : ∀ a, functor.obj a = QuotientSet ((rings X).obj a) (M.presheaf.obj a)
  restriction : ∀ {a b : (AffinePoint X)ᵒᵖ} (f : a ⟶ b) (q : QuotientAt M a),
    ∃ p : QuotientAt M b,
      IsQuotientPullback ((rings X).map f).hom (M.presheaf.restrictₛₗ f) q p ∧
      functor.map f (cast (object_eq a).symm (Quotient.mk _ q)) =
        cast (object_eq b).symm (Quotient.mk _ p)

def projectiveForget {X : Stack S} {M : FPModule X} (F : ProjectivePresheaf M) :
    F.functor.Elementsᵒᵖ ⥤ AffinePoint X :=
  (Functor.Elements.π F.functor).leftOp

structure ProjectiveBundle {X : Stack S} (M : FPModule X) where
  points : ProjectivePresheaf M
  total : Stack S
  projection : StackHom total X
  comparison : AffinePoint total ≌ points.functor.Elementsᵒᵖ
  overBase : comparison.functor ⋙ projectiveForget points ≅ affineMap projection
  fibres : ∀ (T : Over S) (x : X.Fibre T), SchemeFibreModel projection T x

/-- The exact global factorization required in Kresch's convention. -/
structure ProjectiveMorphism {X Y : Stack S} (f : StackHom X Y) where
  sheaf : FPModule Y
  space : ProjectiveBundle sheaf
  embedding : StackHom X space.total
  closed : StackFibreModels.IsClosed embedding
  factorization : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp embedding space.projection) f

end AlgebraicGeometry.StackProjectiveModels
