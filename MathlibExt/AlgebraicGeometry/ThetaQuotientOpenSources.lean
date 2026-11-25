/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaTraitCharts
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Actual punctured quotient sources and their lifting comparisons

The open source is the full subgroupoid of quotient points whose entire
equivariant torsor map lands in the specified open. Its strong map to
the quotient source and every fibre functor are normalized through that
literal full inclusion. The Θ and ST punctures use the actual affine
D(π) ∪ D(X) and D(s) ∪ D(t) opens.

The lifting condition is the native comparison to the actual
isomorphism-comma groupoid, retaining both arrows and the compatible
2-isomorphism. It contains no good-moduli-space conclusion.

Reference: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5,
Definitions 3.10 and 3.38.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ThetaQuotientOpenSources

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open GroupTorsorGeometry ThetaQuotientSources StackSourceFiltrations
open scoped Pseudofunctor.StrongTrans

universe u
variable {R : Type u} [CommRing R]
variable {G W : Over (Spec (.of R))} [GrpObj G] [ModObj G W]

def landsIn (V : W.left.Opens) (T : Over (Spec (.of R))) :
    ObjectProperty (QuotientObject G W T) :=
  fun P => P.map.left ⁻¹ᵁ V = ⊤

/-- The actual full quotient-point groupoid cut, retaining all stabilizers. -/
abbrev OpenPoints (V : W.left.Opens) (T : Over (Spec (.of R))) :=
  (landsIn (G := G) V T).FullSubcategory

/-- A model of the substack of the quotient stack $[W/G]$ (given by the quotient source $Q$) of the
points whose equivariant map lands in an open $V \subseteq W$: a stack over $\operatorname{Spec} R$
with a morphism to the stack of $Q$ and, for every $R$-scheme $T$, an equivalence between its fibre
over $T$ and the full subcategory of quotient points over $T$ (a $G$-torsor $P \to T$ with a
$G$-equivariant map $P \to W$) whose map $P \to W$ lands in $V$, compatible up to isomorphism with
the fibre equivalence of $Q$ through the inclusion of that full subcategory. -/
structure OpenSource (Q : QuotientSource R (G := G) (W := W)) (V : W.left.Opens) where
  stack : RelativeStack (Spec (.of R))
  inclusion : stack.toPseudofunctor ⟶ Q.stack.toPseudofunctor
  fibre : ∀ T : Over (Spec (.of R)), stack.Fibre T ≌ OpenPoints (G := G) V T
  normalized : ∀ T : Over (Spec (.of R)),
    (fibre T).functor ⋙ (landsIn (G := G) V T).ι ≅
      (inclusion.app (.mk (op T))).toFunctor ⋙ (Q.fibre T).functor

/-- The actual groupoid-valued lifting predicate for this punctured source. -/
def UniqueLifts {Q : QuotientSource R (G := G) (W := W)} {V : W.left.Opens}
    (P : OpenSource Q V) {X Y : RelativeStack (Spec (.of R))}
    (f : X.toPseudofunctor ⟶ Y.toPseudofunctor) : Prop :=
  HasUniqueDiagramLifts P.inclusion f

end MathlibExt.AlgebraicGeometry.ThetaQuotientOpenSources
