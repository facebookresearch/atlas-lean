/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPrefixUnion

import Lean.Util.CollectAxioms

/-!
# Public original-prefix union clients

Exercise arbitrary proper carriers, the original lower universal properties,
all old-field preservation and the empty-family construction at an arbitrary
original root. No complete goodification or whole-carrier input is supplied.
-/

set_option autoImplicit false

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace OriginalPrefixUnionPublicClient

noncomputable section

open CategoryTheory.SmallObject.OriginalGoodification

variable {P : Type w} [PartialOrder P]
  {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {I : Type w} [Preorder I] (B : LowerSet P)
  (S : I → LowerSet P) (hInto : ∀ i : I, S i ≤ B) (hMono : Monotone S)
  (F : ∀ i : I, Prefix O M chi (S i))
  (hPreserves : ∀ (i j : I) (hij : i ≤ j),
    Preserves O M chi (hMono hij) (F i) (F j))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hCover : ∀ p : B, ∃ i : I, p.1 ∈ S i)

-- A proper original union retains the complete actual prefix, including its genuine tree.
example : Prefix O M chi B :=
  unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover

-- Every original lower subset has its original chosen point and original comparison-cocone UP.
example (D : LowerSet P) (hD : D ≤ B) :
    let r := unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    Nonempty (IsColimit (OriginalLowerComparisonCocone.cocone
      (prefixLabels B r.ord r.below) r.tree.diagram O.diagram r.comparison M D)) :=
  ⟨(unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover).lowerUP D hD⟩

-- The preservation witness includes all old vertex maps and predecessor/cofan/cell comparisons.
example (i : I) :
    Preserves O M chi (hInto i) (F i)
      (unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover) :=
  unionPrefix_preserves O M chi B S hInto hMono F hPreserves hDirected hCover i

-- The actual union comparison keeps its arbitrary original root map.
example (p : B) :
    let r := unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    (r.tree.diagram.obj p).hom ≫ (r.comparison.app p).right =
      (O.diagram.obj p.1).hom := by
  let r := unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover
  let := r.ord
  let : Preorder B := r.ord.toPreorder
  exact Under.w (r.comparison.app p)

-- The complete producer also works without a nonempty-family hypothesis.
example [IsEmpty I] : Prefix O M chi (⊥ : LowerSet P) := by
  let S0 : I → LowerSet P := fun _ => ⊥
  let hM : Monotone S0 := fun _ _ _ => le_refl ⊥
  let F0 : ∀ i : I, Prefix O M chi (S0 i) := fun _ => emptyPrefix O M chi
  exact unionPrefix O M chi ⊥ S0 (fun _ => le_refl ⊥) hM F0
    (fun _ _ _ => Preserves.refl O M chi (emptyPrefix O M chi))
    (fun i _ => isEmptyElim i)
    (fun p => False.elim (LowerSet.notMem_bot p.2))

end

end OriginalPrefixUnionPublicClient

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let some moduleIdx := env.getModuleIdxFor?
      ``CategoryTheory.SmallObject.OriginalGoodification.unionPrefix
    | throwError "The original-prefix union API is not imported"
  let names := env.constants.fold (init := #[]) fun names name _ =>
    if env.getModuleIdxFor? name == some moduleIdx then names.push name else names
  for name in names do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun ax =>
      ax != ``propext && ax != ``Quot.sound && ax != ``Classical.choice
    unless forbidden.isEmpty do
      throwError "Nonstandard axioms in {name}: {forbidden}"
  logInfo m!"Original-prefix union clients: {names.size} actual declarations, standard axioms"
