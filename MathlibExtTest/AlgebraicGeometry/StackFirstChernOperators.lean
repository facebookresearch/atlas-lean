/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.StackFirstChernSchemeComparison
import MathlibExt.AlgebraicGeometry.IntegralGysinRecipes

/-!
# Tests for the stack first Chern cap and the refined Gysin recipe

A supposed zero section cannot represent a nonzero module element, even
through an isomorphism of affine stack points. This catches a translated
zero section which agrees only on the underlying bundle projection.

The first Chern cap of a line bundle lowers the dimension by one, and its
projection pull, before regrading, is the zero-section push. The projection
pull of the refined Gysin map is the closed push of the specialized cone class:
this pins specialization, closed push, inverse pull and the grading together.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open StackCycleGeometry StackCycleRelations StackAffineModules StackVectorBundles StackChowGroups
open StackFirstChernOperators

example {S : Scheme.{0}} {X : Stack S} (E : VectorBundle X)
    (a : AffinePoint X) (m : E.module.val.presheaf.obj (op a)) (nonzero : m ≠ 0) :
    ¬ Nonempty ((StackBundleCones.zeroElementFunctor E).obj a ≅
      op ((sectionPresheaf E.module.val).elementsMk (op a) m)) := by
  rintro ⟨e⟩
  have h := e.inv.unop.map_val
  change E.module.val.presheaf.presheaf.map e.inv.unop.hom 0 = m at h
  rw [map_zero] at h
  exact nonzero h.symm

example {S : Scheme.{0}} {X : Stack S} (E : VectorBundle X)
    (a : AffinePoint X) [Nontrivial ((rings X).obj (op a))]
    (frame : E.module.val.presheaf.obj (op a) ≃ₗ[(rings X).obj (op a)] (rings X).obj (op a)) :
    ¬ Nonempty ((StackBundleCones.zeroElementFunctor E).obj a ≅
      op ((sectionPresheaf E.module.val).elementsMk (op a) (frame.symm 1))) := by
  rintro ⟨e⟩
  have h := e.inv.unop.map_val
  change E.module.val.presheaf.presheaf.map e.inv.unop.hom 0 = frame.symm 1 at h
  rw [map_zero] at h
  have hh := congrArg frame h
  simp at hh

/-- The first Chern cap lowers the dimension by one; before regrading it is the
Euler operator of the line bundle. -/
example {S : Scheme.{0}} {scope : Stack S → Prop} {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) (a : ChowGroup D K X hX d) :
    firstChern C d a = chowRegrade D K X hX (by simp [C.rank_one])
      (StackBundleCones.eulerOperator C.homotopy C.zero C.push d a) :=
  rfl

/-- The projection pull of the Euler operator is the zero-section push. -/
example {S : Scheme.{0}} {scope : Stack S → Prop} {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {X : Stack S} {hX : scope X} {E : VectorBundle X}
    (C : FirstChernData D K hX E) (d : ℤ) (a : ChowGroup D K X hX d) :
    C.homotopy.isomorphism d (StackBundleCones.eulerOperator C.homotopy C.zero C.push d a) =
      C.push.map d a :=
  isomorphism_eulerOperator C d a

open IntegralOperationalChow IntegralGysinRecipes in
/-- The projection pull of the refined Gysin map is the closed push of the
specialized cone class. -/
example {k : Type} [Field k] (O : CycleOperations (k := k))
    {Z Y T : IntegerSchemeChow.FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {t : T.scheme ⟶ Y.scheme} {c : ℕ}
    (G : RefinedGeometry O i t c) (S : Specialization O G) (d : ℤ)
    (a : IntegerSchemeChow.ChowGroup T d) :
    pulledBundlePullback O G.pulledBundle d (refinedGysin O G S d a) =
      O.proper G.embedding d (S.map d a) :=
  (AddEquiv.ofBijective (pulledBundlePullback O G.pulledBundle d)
    (G.pulledBundle.inverse d)).apply_symm_apply _
