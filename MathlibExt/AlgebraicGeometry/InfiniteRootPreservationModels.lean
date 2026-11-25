/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.InfiniteRootSectionModels
public import MathlibExt.AlgebraicGeometry.RootEtaleRestrictions

/-!
# Universal infinite-root preservation on geometric fibres

Base change is the literal Over.map-precomposition of the original
relative pseudofunctor. A base-changed arrow fixes every component and
every native naturality cell. Section pullback uses actual cartesian
module precomposition and the native structure-module comparison.

Preservation quantifies every infinite root on each entire geometric
target fibre. Its section test uses all affine scheme families over the
geometric field, including nilpotents. Neither positive universal
generators alone nor field-point section values replace this test.

Source: Talpo--Vistoli arXiv:1410.1164v2, Definitions5.1 and5.20.
Ordinary fppf-stack base-change assembly is separate source integration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.InfiniteRootPreservationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.CartesianStackModules
open InfiniteRootSectionModels FiniteRootTowers

variable {S : Scheme.{0}}

/-- Base changes of the stack $R$ over $S$ are stacks: an instance of this class asserts that, for
every morphism of schemes $b : T \to S$, the base change of $R$ along $b$, obtained by composing $R$
with the functor from schemes over $T$ to schemes over $S$ induced by $b$
(`RootEtaleRestrictions.pseudofunctor b R`), is a stack for the fppf topology over $T$. -/
class HasBaseChanges (R : Stack S) : Prop where
  isStack : ∀ (T : Scheme.{0}) (b : T ⟶ S),
    (RootEtaleRestrictions.pseudofunctor b R).IsStack (Scheme.fppfTopology.over T)

attribute [instance] HasBaseChanges.isStack

def baseChanged (R : Stack S) [HasBaseChanges R] {T : Scheme.{0}} (b : T ⟶ S) : Stack T :=
  RootEtaleRestrictions.stack b R

variable {X Y : Stack S} [HasBaseChanges X] [HasBaseChanges Y]

/-- Every functor and naturality component is the original arrow on the
original base-changed test scheme. Only bicategorical assembly remains. -/
structure BaseChangedMap (f : StackHom X Y) {T : Scheme.{0}} (b : T ⟶ S) where
  morphism : StackHom (baseChanged X b) (baseChanged Y b)
  components : ∀ U : Over T, StackCycleGeometry.component morphism U =
    StackCycleGeometry.component f ((Over.map b).obj U)
  naturalities : ∀ {U V : Over T} (g : U ⟶ V),
    HEq (morphism.naturality g.op.toLoc)
      (f.naturality ((Over.map b).map g).op.toLoc)

/-- Literal pullback of the original section through the native unit comparison. -/
def sectionPullback (f : StackHom X Y) {L : QCoh Y} (s : structureModule Y ⟶ L) :
    structureModule X ⟶ (pullback f).obj L :=
  (pullbackStructure f).inv ≫ (pullback f).map s

/-- Definition5.20 on the whole geometric-fibre category. The target
tensor certificates refer only to the fixed native cartesian tensor. -/
def IsRootPreserving (f : StackHom X Y)
    (B : ∀ (T : Scheme.{0}) (b : T ⟶ S), BaseChangedMap f b)
    (TY : ∀ (T : Scheme.{0}) (b : T ⟶ S), HasTensorLanding (baseChanged Y b)) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (A : @InfiniteRoot (Spec (.of Ω)) (baseChanged Y x) (TY _ x)),
    ∃ N : Exponent, ∀ n : Exponent, N.val ∣ n.val →
      GeometricNonzero (baseChanged X x) (𝟙 (Spec (.of Ω)))
        (sectionPullback (B _ x).morphism (A.sectionMap n))

end MathlibExt.AlgebraicGeometry.InfiniteRootPreservationModels
