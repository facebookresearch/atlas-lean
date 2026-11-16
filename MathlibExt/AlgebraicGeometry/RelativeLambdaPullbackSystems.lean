/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LambdaConnectionStability

/-!
# Actual coherent reindexing systems for relative framed lambda families

Every reindexing is the existing section-normalized native bundle pullback.
The square is the literal product square, the frame is the literal {x}×T
restriction, and both connection degrees have their existing generator
normalizations. The identity and composition comparisons are actual bundle,
operator, parameter and frame isomorphisms. No moduli representability,
semistability preservation or nonabelian Hodge theorem is an input field.

Source: Simpson, alg-geom/9604005v1, section 4 and Proposition 4.1;
the imported relative module/form/base-change definitions retain their
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 and
Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b source/license credits.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeLambdaPullbackSystems

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open RelativeFramedLambdaFamilies RelativeLambdaReindexing
open RelativeDeRhamDifferential RelativeDifferentialForms
open PerverseSheaves

variable (X : ComplexScheme) (x : 𝟙_ ComplexScheme ⟶ X) (n : ℕ)

structure PullbackSystem where
  differential : ∀ T : ComplexScheme, Differential (projection X T)
  square : ∀ {S T : ComplexScheme} (f : S ⟶ T), ProductBaseChange X f
  tensor : ∀ {S T : ComplexScheme} (f : S ⟶ T),
    TensorPullbackComparison (square f).square.total
  formComparison : ∀ {S T : ComplexScheme} (f : S ⟶ T),
    FormBaseChange (square f).square (tensor f) (differential T) (differential S)
  free : ∀ {S T : ComplexScheme} (f : S ⟶ T), FreePullbackComparison f n
  lift : ∀ {S T : ComplexScheme} (f : S ⟶ T) (E : Family X x T (differential T) n),
    PulledFamily X x f (square f) (tensor f) (free f) (formComparison f) E

def PullbackSystem.pull (P : PullbackSystem X x n) {S T : ComplexScheme}
    (f : S ⟶ T) (E : Family X x T (P.differential T) n) : Family X x S (P.differential S) n :=
  PulledFamily.family X x f (P.square f) (P.tensor f) (P.free f) (P.formComparison f) E (P.lift f E)

/-- Coherence retains the native parameter, bundle, BOTH operators and frame
through `Family.Iso`; equality of only underlying isomorphism classes is weaker. -/
structure PullbackCoherence (P : PullbackSystem X x n) : Prop where
  identity : ∀ (T : ComplexScheme) (E : Family X x T (P.differential T) n),
    Nonempty (Family.Iso (P.pull X x n (𝟙 T) E) E)
  composition : ∀ {R S T : ComplexScheme} (f : R ⟶ S) (g : S ⟶ T)
      (E : Family X x T (P.differential T) n),
    Nonempty (Family.Iso (P.pull X x n f (P.pull X x n g E)) (P.pull X x n (f ≫ g) E))

def openBase (T : ComplexScheme) (U : T.left.Opens) : ComplexScheme := Over.mk (U.ι ≫ T.hom)

def openInclusion (T : ComplexScheme) (U : T.left.Opens) : openBase T U ⟶ T := Over.homMk U.ι rfl

def restrictFamily (P : PullbackSystem X x n) {T : ComplexScheme}
    (E : Family X x T (P.differential T) n) (U : T.left.Opens) :
    Family X x (openBase T U) (P.differential (openBase T U)) n :=
  P.pull X x n (openInclusion T U) E

end MathlibExt.AlgebraicGeometry.RelativeLambdaPullbackSystems
