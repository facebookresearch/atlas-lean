/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

meta import Lean.Elab.Tactic.Simproc

import MathlibExt.Algebra.Homology.HomologySequenceFunctor

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerPairSequence

/-!
# Integer-graded singular homology data
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The integer-graded connecting morphism of the singular pair sequence in
two adjacent degrees. -/
noncomputable def relativeSingularBoundaryIntRel (R : C) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    relativeSingularHomologyIntFunctor C R i ⟶
      TopPair.proj₂ ⋙ singularHomologyIntFunctor C R j :=
  HomologicalComplex.HomologySequence.δNatTransOfFamily
    (singularPairShortComplexIntFunctor C R)
    (singularPairShortComplexIntFunctor_obj_shortExact C R) i j hij

@[simp↓]
lemma relativeSingularBoundaryIntRel_app (R : C) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) (P : TopPair.{w}) :
    (relativeSingularBoundaryIntRel C R i j hij).app P =
      (singularPairShortComplexIntFunctor_obj_shortExact C R P).δ i j hij := rfl

noncomputable instance isIso_singularPairShortComplexInt_g_of_isEmpty
    (R : C) (P : TopPair.{w}) [IsEmpty P.snd] :
    IsIso ((singularPairShortComplexIntFunctor C R).obj P).g := by
  change IsIso ((ComplexShape.embeddingDownNatToIntExtendFunctor C).map
    ((singularPairShortComplexFunctor C R).obj P).g)
  infer_instance

/-- Integer-graded relative homology of `(X, ∅)` agrees naturally with absolute homology. -/
noncomputable def singularHomologyEmptyPairIntIso (R : C) (z : ℤ) :
    singularHomologyIntFunctor C R z ≅
      TopPair.incl ⋙ relativeSingularHomologyIntFunctor C R z :=
  NatIso.ofComponents
    (fun X => by
      haveI : IsEmpty (TopPair.incl.obj X).snd := inferInstanceAs (IsEmpty PEmpty)
      exact HomologicalComplex.homologyMapIso
        (asIso ((singularPairShortComplexIntFunctor C R).obj
          (TopPair.incl.obj X)).g) z)
    (fun {X Y} f => by
      change (singularHomologyIntFunctor C R z).map f ≫
          HomologicalComplex.homologyMap
            ((singularPairShortComplexIntFunctor C R).obj
              (TopPair.incl.obj Y)).g z =
        HomologicalComplex.homologyMap
            ((singularPairShortComplexIntFunctor C R).obj
              (TopPair.incl.obj X)).g z ≫
          (relativeSingularHomologyIntFunctor C R z).map (TopPair.incl.map f)
      exact ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) z).mapShortComplex.map
        ((singularPairShortComplexIntFunctor C R).map (TopPair.incl.map f))).comm₂₃)

/-- Raw integer-graded singular homology data for the Eilenberg--Steenrod hierarchy. -/
-- Concrete projections must reduce when matching native component composition.
@[reducible]
noncomputable def singularHomologyIntData (R : C) :
    TopPair.HomologyTheoryData.{w} C where
  Hₚ z := relativeSingularHomologyIntFunctor C R z
  H z := singularHomologyIntFunctor C R z
  iso z := singularHomologyEmptyPairIntIso C R z
  δ i j := if hrel : (ComplexShape.down ℤ).Rel i j then
      relativeSingularBoundaryIntRel C R i j hrel else 0
  shape_δ _ _ h := dite_eq_right h

@[simp]
lemma singularHomologyIntData_Hₚ (R : C) (z : ℤ) :
    (singularHomologyIntData C R).Hₚ z =
      relativeSingularHomologyIntFunctor C R z := rfl

@[simp]
lemma singularHomologyIntData_H (R : C) (z : ℤ) :
    (singularHomologyIntData C R).H z = singularHomologyIntFunctor C R z := rfl

@[simp]
lemma singularHomologyIntData_iso (R : C) (z : ℤ) :
    (singularHomologyIntData C R).iso z = singularHomologyEmptyPairIntIso C R z := rfl

/-- Compatibility simp rule for callers carrying a shape-relation witness.
The normalized equation rule below covers the simplified relation form. -/
@[simp, nolint simpNF]
lemma singularHomologyIntData_δ_of_rel (R : C) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    (singularHomologyIntData C R).δ i j =
      relativeSingularBoundaryIntRel C R i j hij := by
  simp only [singularHomologyIntData]
  rw [dite_eq_left hij]

/-- Explicit adjacent-degree equality with the connecting transformation.
The scoped boundary procedure supplies the default simplification. -/
lemma singularHomologyIntData_δ_of_eq (R : C) (i j : ℤ) (hij : j + 1 = i) :
    (singularHomologyIntData C R).δ i j =
      relativeSingularBoundaryIntRel C R i j
        (by simpa only [ComplexShape.down_Rel] using hij) :=
  singularHomologyIntData_δ_of_rel C R i j
    (by simpa only [ComplexShape.down_Rel] using hij)

/-- On a shape edge, the boundary-data component is the connecting morphism
of the integer singular-pair short exact sequence. -/
lemma singularHomologyIntData_δ_app_of_rel (R : C) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) (P : TopPair.{w}) :
    ((singularHomologyIntData C R).δ i j).app P =
      (singularPairShortComplexIntFunctor_obj_shortExact C R P).δ i j hij := by
  rw [singularHomologyIntData_δ_of_rel C R i j hij,
    relativeSingularBoundaryIntRel_app]

/-- Preserve the relation-witness component equality before simplification
changes the dependent source and target objects of its morphisms. -/
@[simp↓]
lemma singularHomologyIntData_δ_app_eq_boundary_iff_true
    (R : C) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j)
    (P : TopPair.{w}) :
    (((singularHomologyIntData C R).δ i j).app P =
      (relativeSingularBoundaryIntRel C R i j hij).app P) ↔ True := by
  apply iff_true_intro
  exact congrArg
    (fun α : (singularHomologyIntData C R).Hₚ i ⟶
        TopPair.proj₂ ⋙ (singularHomologyIntData C R).H j => α.app P)
    (singularHomologyIntData_δ_of_rel C R i j hij)

/-- Explicit data-typed wrapper for the integer connecting transformation.
It retains compatibility for callers working with the data's endpoint functors. -/
noncomputable def singularHomologyIntDataBoundary (R : C) (i j : ℤ) :
    (singularHomologyIntData C R).Hₚ i ⟶
      TopPair.proj₂ ⋙ (singularHomologyIntData C R).H j :=
  (singularHomologyIntData C R).δ i j

/-- Explicit compatibility equality between the boundary field and its data-typed wrapper. -/
lemma singularHomologyIntData_δ_eq_boundary (R : C) (i j : ℤ) :
    (singularHomologyIntData C R).δ i j =
      singularHomologyIntDataBoundary C R i j :=
  rfl

/-- Explicit compatibility equality for a raw connecting transformation. -/
lemma relativeSingularBoundaryIntRel_eq_dataBoundary
    (R : C) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    relativeSingularBoundaryIntRel C R i j hij =
      singularHomologyIntDataBoundary C R i j :=
  (singularHomologyIntData_δ_of_rel C R i j hij).symm

/-- The canonical data-typed normal form vanishes away from the complex
shape relation. -/
@[simp↓]
lemma singularHomologyIntDataBoundary_eq_zero (R : C) (i j : ℤ)
    (hij : j + 1 ≠ i) :
    singularHomologyIntDataBoundary C R i j = 0 := by
  unfold singularHomologyIntDataBoundary
  exact (singularHomologyIntData C R).shape_δ i j
    (by simpa only [ComplexShape.down_Rel] using hij)

/-- Apply the boundary equality before recursively simplifying its shape proof
or dependent endpoint functors. -/
@[simp↓]
lemma singularHomologyIntData_δ_eq_boundary_iff_true
    (R : C) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    ((singularHomologyIntData C R).δ i j =
      relativeSingularBoundaryIntRel C R i j hij) ↔ True := by
  rw [iff_true]
  exact singularHomologyIntData_δ_of_rel C R i j hij

/-- Apply off-shape vanishing before recursively simplifying the dependent
endpoint functors of the zero morphism. -/
@[simp↓]
lemma singularHomologyIntData_δ_eq_zero_iff_true
    (R : C) (i j : ℤ) (hij : j + 1 ≠ i) :
    ((singularHomologyIntData C R).δ i j = 0) ↔ True := by
  rw [iff_true]
  exact (singularHomologyIntData C R).shape_δ i j
    (by simpa only [ComplexShape.down_Rel] using hij)

@[simp]
lemma singularHomologyIntData_subspaceMap (R : C) (z : ℤ) (P : TopPair.{w}) :
    (singularHomologyIntData C R).subspaceMap z P =
      HomologicalComplex.homologyMap
        ((singularPairShortComplexIntFunctor C R).obj P).f z := rfl

@[simp]
lemma singularHomologyIntData_toRelative (R : C) (z : ℤ) (P : TopPair.{w}) :
    (singularHomologyIntData C R).toRelative z P =
      HomologicalComplex.homologyMap
        ((singularPairShortComplexIntFunctor C R).obj P).g z := by
  change HomologicalComplex.homologyMap
      ((singularPairShortComplexIntFunctor C R).obj (TopPair.incl.obj P.fst)).g z ≫
        HomologicalComplex.homologyMap
          ((singularPairShortComplexIntFunctor C R).map (TopPair.j P)).τ₃ z =
    HomologicalComplex.homologyMap
      ((singularPairShortComplexIntFunctor C R).obj P).g z
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  have h := ((singularPairShortComplexIntFunctor C R).map (TopPair.j P)).comm₂₃.symm
  change ((singularPairShortComplexIntFunctor C R).obj
      (TopPair.incl.obj P.fst)).g ≫
        ((singularPairShortComplexIntFunctor C R).map (TopPair.j P)).τ₃ =
      (singularChainIntFunctor C R).map (𝟙 P.fst) ≫
        ((singularPairShortComplexIntFunctor C R).obj P).g at h
  rw [(singularChainIntFunctor C R).map_id P.fst] at h
  exact h.trans (Category.id_comp _)

/-- In a nonnegative degree, conjugating the integer-graded `toRelative` map
by the Nat-to-Int comparison isomorphisms recovers the homology map induced by
the ordinary relative-chain quotient. -/
theorem singularHomologyIntData_toRelative_natAgreement
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) (P : TopPair.{w}) :
    ((singularHomologyNatToIntIso C R n).app P.fst).inv ≫
        (singularHomologyIntData C R).toRelative (n : ℤ) P ≫
        ((relativeSingularHomologyNatToIntIso C R n).app P).hom =
      HomologicalComplex.homologyMap
        (relativeSingularChainQuotient C R P) n := by
  rw [singularHomologyIntData_toRelative]
  change
    ((singularHomologyNatToIntIso C R n).app P.fst).inv ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainIntQuotient C R P) (n : ℤ) ≫
        ((relativeSingularHomologyNatToIntIso C R n).app P).hom =
      HomologicalComplex.homologyMap
        (relativeSingularChainQuotient C R P) n
  let eAbs := (singularHomologyNatToIntIso C R n).app P.fst
  let eRel := (relativeSingularHomologyNatToIntIso C R n).app P
  let qInt := HomologicalComplex.homologyMap
    (relativeSingularChainIntQuotient C R P) (n : ℤ)
  let qNat := HomologicalComplex.homologyMap
    (relativeSingularChainQuotient C R P) n
  have hCompat : eAbs.hom ≫ qNat = qInt ≫ eRel.hom :=
    singularHomologyNatToIntIso_relativeQuotient C R P n
  change eAbs.inv ≫ (qInt ≫ eRel.hom) = qNat
  have hPre : eAbs.inv ≫ (qInt ≫ eRel.hom) =
      eAbs.inv ≫ (eAbs.hom ≫ qNat) :=
    congrArg (fun m => eAbs.inv ≫ m) hCompat.symm
  exact hPre.trans (eAbs.inv_hom_id_assoc qNat)

/-- The Nat-to-Int agreement for `toRelative` after explicitly transporting
an equal presentation of its absolute source in both integer and natural grading. -/
theorem singularHomologyIntData_toRelative_natAgreement_cast_fst
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) (S : TopCat.{w}) (P : TopPair.{w}) (hS : S = P.fst) :
    let intCast := eqToHom (congrArg
      (fun X => (singularHomologyIntFunctor C R (n : ℤ)).obj X) hS)
    let natCast := eqToHom (congrArg
      (fun X => ((singularHomologyFunctor C n).obj R).obj X) hS)
    ((singularHomologyNatToIntIso C R n).app S).inv ≫
        intCast ≫
          (singularHomologyIntData C R).toRelative (n : ℤ) P ≫
            ((relativeSingularHomologyNatToIntIso C R n).app P).hom =
      natCast ≫ HomologicalComplex.homologyMap
        (relativeSingularChainQuotient C R P) n := by
  subst S
  simp only [eqToHom_refl, Category.id_comp]
  exact (singularHomologyIntData_toRelative_natAgreement C R n P).trans
    (Category.id_comp _).symm

@[simp]
lemma singularHomologyIntData_boundary (R : C) (z : ℤ) (P : TopPair.{w}) :
    (singularHomologyIntData C R).boundary z P =
      (relativeSingularBoundaryIntRel C R z (z - 1) (by simp)).app P := by
  simp only [TopPair.HomologyTheoryData.boundary, singularHomologyIntData]
  rw [dite_eq_left (by simp)]

/-- The direct integer pair connecting morphism agrees with the natural one
conjugated by the Nat-to-Int comparison isos. -/
theorem relativeSingularBoundaryIntRel_natAgreement
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) (P : TopPair.{w}) :
    (relativeSingularBoundaryIntRel C R ((n + 1 : ℕ) : ℤ) (n : ℤ) (by simp)).app P =
      ((relativeSingularHomologyNatToIntIso C R (n + 1)).app P).hom ≫
        (relativeSingularBoundary C R n).app P ≫
        ((singularHomologyNatToIntIso C R n).app (P.snd)).inv := by
  have hbase := ShortComplex.ShortExact.delta_extendDownNatToInt
    ((singularPairShortComplexFunctor C R).obj P)
    (singularPairShortComplex_shortExact C R P)
    n (by simp) (by simp)
  have hiso : (ShortComplex.ShortExact.map_extendFunctor
        ComplexShape.embeddingDownNatToInt
        ((singularPairShortComplexFunctor C R).obj P)
        (singularPairShortComplex_shortExact C R P)).δ
          (((n + 1 : ℕ) : ℤ)) ((n : ℤ)) (by simp) =
        (((singularPairShortComplexFunctor C R).obj P).X₃.extendHomologyIso
          ComplexShape.embeddingDownNatToInt rfl).hom ≫
        (singularPairShortComplex_shortExact C R P).δ (n + 1) n (by simp) ≫
        ((((singularPairShortComplexFunctor C R).obj P).X₁.extendHomologyIso
          ComplexShape.embeddingDownNatToInt rfl).inv) :=
    let I₁ := ((((singularPairShortComplexFunctor C R).obj P).X₁.extendHomologyIso
      ComplexShape.embeddingDownNatToInt rfl));
    Eq.trans
      (Eq.symm
        (Eq.trans (Eq.trans (Category.assoc _ _ _)
          (congrArg (fun φ => _ ≫ φ) (Iso.hom_inv_id I₁)))
          (Category.comp_id _)))
      (Eq.trans (congrArg (fun φ => φ ≫ I₁.inv) hbase.symm)
        (Category.assoc _ _ _))
  change (relativeSingularBoundaryIntRel C R _ _ _).app P = _
  rw [relativeSingularBoundaryIntRel_app]
  unfold relativeSingularBoundary
  exact hiso

/-- The integer empty-pair comparison conjugates the natural one by the
Nat-to-Int comparison maps. -/
theorem singularHomologyEmptyPairIntIso_hom_conj_natToInt
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) (X : TopCat.{w}) :
    (singularHomologyEmptyPairIntIso C R (n : ℤ)).hom.app X ≫
      (relativeSingularHomologyNatToIntIso C R n).hom.app
        (TopPair.incl.obj X) =
    (singularHomologyNatToIntIso C R n).hom.app X ≫
      (singularHomologyEmptyPairIso C R n).hom.app X := by
  have hnat := homologyIso_extendDownNatToInt_naturality
    (((singularPairShortComplexFunctor C R).obj (TopPair.incl.obj X)).g) n
  dsimp only [singularHomologyEmptyPairIntIso, singularHomologyEmptyPairIso,
    relativeSingularHomologyNatToIntIso, singularHomologyNatToIntIso,
    homologyIsoExtendDownNatToInt, CategoryTheory.NatIso.ofComponents,
    HomologicalComplex.homologyMapIso, asIso]
  exact hnat

end AlgebraicTopology

namespace AlgebraicTopology

meta section
open Lean Meta Simp

private def singularHomologyIntDataShapeProof? (proof rel : Expr) : SimpM (Option Expr) := do
  let type ← inferType proof
  if ← withSimpMetaConfig (isDefEq type rel) then
    return some proof
  if let some (_, lhs, rhs) := type.eq? then
    if rhs.isTrue && (← withSimpMetaConfig (isDefEq lhs rel)) then
      return some (← mkOfEqTrue proof)
  return none

private def singularHomologyIntDataRelWitness? (rel : Expr) : SimpM (Option Expr) := do
  let ctx ← getContext
  let lctx ← getLCtx
  -- Explicit supplied facts are used with their actual simp origins.
  for thms in ctx.simpTheorems do
    let candidates :=
      (← withSimpIndexConfig <| thms.pre.getMatchWithExtra rel) ++
        (← withSimpIndexConfig <| thms.post.getMatchWithExtra rel)
    for (thm, _) in candidates do
      if thms.erased.contains thm.origin then continue
      match thm.origin with
      | .stx .. => pure ()
      | .fvar id =>
          let some decl := lctx.find? id | continue
          if decl.isImplementationDetail ||
              (!ctx.config.contextual && decl.index >= ctx.lctxInitIndices) then continue
      | _ => continue
      try
        if let some proof ← singularHomologyIntDataShapeProof? (← thm.getValue) rel then
          recordSimpTheorem thm.origin
          return some proof
      catch _ => pure ()
  -- As in the native assumption guard, newly introduced hypotheses are
  -- available only when contextual simplification is explicitly enabled.
  let proof? ← lctx.findDeclRevM? fun decl => do
    if decl.isImplementationDetail then return none
    if !ctx.config.contextual && decl.index >= ctx.lctxInitIndices then return none
    if ctx.simpTheorems.any (fun thms => thms.erased.contains (.fvar decl.fvarId)) then
      return none
    if ← withSimpMetaConfig (isDefEq rel decl.type) then return some decl.toExpr
    return none
  if let some proof := proof? then
    recordSimpTheorem (.fvar proof.fvarId!)
  return proof?

end

open Lean Meta Simp

/-- Evaluate the concrete integer singular-homology boundary using an explicitly
supplied simp fact or an eligible initial-local shape witness. Thus bare `simp`
can use an available initial-local `Rel` hypothesis. The returned equality is
`singularHomologyIntData_δ_of_rel`; the procedure is limited to this DATA field. -/
simproc ↓ singularHomologyIntDataDelta
    ((AlgebraicTopology.singularHomologyIntData _ _).δ _ _) :=
  fun e => do
    let args := e.getAppArgs
    if args.size < 2 || e.hasExprMVar then return .continue
    let data? := match e.getAppFn with
      | .proj ``TopPair.HomologyPretheory 3 data => some data
      | .const ``TopPair.HomologyPretheory.δ _ =>
          if args.size < 3 then none else some args[args.size - 3]!
      | _ => none
    let some data := data? | return .continue
    unless data.getAppFn.isConstOf ``AlgebraicTopology.singularHomologyIntData do
      return .continue
    if (← getContext).simpTheorems.any
        (fun thms => thms.erased.contains (.decl
          ``AlgebraicTopology.singularHomologyIntData_δ_of_rel)) then return .continue
    let i := args[args.size - 2]!
    let j := args[args.size - 1]!
    let dataType ← whnf (← inferType data)
    let_expr TopPair.HomologyPretheory _ _ _ _ shape := dataType | return .continue
    let rel ← mkAppM ``ComplexShape.Rel #[shape, i, j]
    let some witness ← singularHomologyIntDataRelWitness? rel | return .continue
    let proof ← mkAppOptM ``AlgebraicTopology.singularHomologyIntData_δ_of_rel
      ((data.getAppArgs.map some) ++ #[some i, some j, some witness])
    let proof ← instantiateMVars proof
    let some (_, lhs, rhs) := (← inferType proof).eq? | return .continue
    unless ← withSimpMetaConfig (isDefEq e lhs) do return .continue
    recordSimpTheorem (.decl ``AlgebraicTopology.singularHomologyIntData_δ_of_rel)
    return .visit { expr := rhs, proof? := some proof }

end AlgebraicTopology
