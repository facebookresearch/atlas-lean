/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexCoordinates
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Boundary lifting for the original full groupoid simplexes

Every original boundary map into `J[n]` extends by its complete vertex tuple.
The resulting actual projection to `Δ[0]` is a trivial fibration. The native
ordinal nerve contraction then proves weakness of the original simplex
inclusion and of the represented original k comparison.

Source: Joyal, *The theory of quasi-categories*, Theorem 9.13, representable
weak-comparison clause. Global k-comparison weakness and categorical
preservation are separate statements.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FreeGroupoidSimplex

private theorem stdVertex_apply (m : ℕ) (r : Fin (m + 1)) (i : Fin 1) :
    (stdSimplex.obj₀Equiv.symm r : (Δ[m] : SSet.{u}) _⦋0⦌) i = r := rfl

private def boundaryVertex (m : ℕ) (hm : 0 < m) (r : Fin (m + 1)) :
    (boundary.{u} m : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm r, by
    rw [mem_boundary_iff_notMem_range]
    by_cases hr : r = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rintro ⟨i, hi⟩
      have he : r = ⟨1, by omega⟩ := (stdVertex_apply.{u} m r i).symm.trans hi
      have hv := congrArg Fin.val he
      simp only [hr, Fin.val_zero] at hv
      omega
    · refine ⟨0, ?_⟩
      rintro ⟨i, hi⟩
      exact hr ((stdVertex_apply.{u} m r i).symm.trans hi)⟩

private def vertexOperator {d : ℕ} (r : Fin (d + 1)) : ⦋0⦌ ⟶ ⦋d⦌ :=
  ⦋0⦌.const ⦋d⦌ r

private theorem boundary_vertex_operator {m d : ℕ} (hm : 0 < m)
    (x : (boundary.{u} m : SSet.{u}) _⦋d⦌) (r : Fin (d + 1)) :
    (boundary m : SSet.{u}).map (vertexOperator r).op x =
      boundaryVertex m hm (x.val r) := by
  apply Subtype.ext
  apply stdSimplex.obj₀Equiv.injective
  rfl

private def boundaryLabels (n : SimplexCategory) {m : ℕ} (hm : 0 < m)
    (t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n) :
    Fin (m + 1) → Fin (n.len + 1) :=
  fun r => simplexVertexEquiv n 0 (t.app (op ⦋0⦌) (boundaryVertex m hm r)) 0

private def positiveBoundaryFiller (n : SimplexCategory) {m : ℕ} (hm : 0 < m)
    (t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n) : (Δ[m] : SSet.{u}) ⟶ J.obj n :=
  SSet.yonedaEquiv.symm ((simplexVertexEquiv n m).symm (boundaryLabels n hm t))

private theorem positiveBoundaryFiller_coord (n : SimplexCategory) {m d : ℕ}
    (hm : 0 < m) (t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n)
    (x : (Δ[m] : SSet.{u}) _⦋d⦌) (r : Fin (d + 1)) :
    simplexVertexEquiv n d ((positiveBoundaryFiller n hm t).app (op ⦋d⦌) x) r =
      boundaryLabels n hm t (x r) := by
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.{u}.symm.surjective x
  change simplexVertexEquiv.{u} n d
    ((SSet.yonedaEquiv.{u}.symm ((simplexVertexEquiv.{u} n m).symm
      (boundaryLabels n hm t))).app (op ⦋d⦌) (stdSimplex.objEquiv.symm f)) r = _
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm.{u}]
  rw [simplexVertexEquiv_operator.{u}]
  simp only [Equiv.apply_symm_apply]
  rfl

private theorem positiveBoundaryFiller_fac (n : SimplexCategory) {m : ℕ}
    (hm : 0 < m) (t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n) :
    (boundary m).ι ≫ positiveBoundaryFiller n hm t = t := by
  apply SSet.hom_ext
  intro Δ
  obtain ⟨d⟩ := Δ
  induction d using SimplexCategory.rec with | _ d
  ext x
  apply (simplexVertexEquiv n d).injective
  funext r
  change simplexVertexEquiv n d ((positiveBoundaryFiller n hm t).app (op ⦋d⦌) x.val) r =
    simplexVertexEquiv n d (t.app (op ⦋d⦌) x) r
  rw [positiveBoundaryFiller_coord]
  have hnat := congrArg
    (fun f : (boundary m : SSet.{u}).obj (op ⦋d⦌) ⟶ (J.obj n).obj (op ⦋0⦌) => f x)
    (t.naturality (vertexOperator r).op)
  change t.app (op ⦋0⦌) ((boundary m : SSet.{u}).map (vertexOperator r).op x) =
    (J.obj n).map (vertexOperator r).op (t.app (op ⦋d⦌) x) at hnat
  rw [boundary_vertex_operator hm x r] at hnat
  have h := congrArg (fun z => simplexVertexEquiv n 0 z 0) hnat
  rw [simplexVertexEquiv_operator] at h
  exact h

/-- The original full-J projection to the standard simplicial point. -/
def JZeroProjection (n : SimplexCategory) : J.{u}.obj n ⟶ (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.from _

/-- Every original boundary square into full J has an actual lift with both factors. -/
@[no_expose] def JBoundaryLift (n : SimplexCategory) {m : ℕ}
    {t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n}
    {b : (Δ[m] : SSet.{u}) ⟶ (Δ[0] : SSet.{u})}
    (sq : CommSq t (boundary m).ι (JZeroProjection n) b) : sq.LiftStruct := by
  cases m with
  | zero =>
    refine
      { l := SSet.yonedaEquiv.symm (vertex n 0)
        fac_left := ?_
        fac_right := stdSimplex.isTerminalObj₀.hom_ext _ _ }
    apply SSet.hom_ext
    intro Δ
    obtain ⟨d⟩ := Δ
    induction d using SimplexCategory.rec with | _ d
    ext x
    have hx : x.val ∈ (⊥ : (Δ[0] : SSet.{u}).Subcomplex).obj (op ⦋d⦌) := by
      simpa only [boundary_zero] using x.property
    exact False.elim hx
  | succ m =>
    exact
      { l := positiveBoundaryFiller n (Nat.zero_lt_succ m) t
        fac_left := positiveBoundaryFiller_fac n (Nat.zero_lt_succ m) t
        fac_right := stdSimplex.isTerminalObj₀.hom_ext _ _ }

/-- The boundary lift retains the whole prescribed top map. -/
@[reassoc]
theorem JBoundaryLift_fac_left (n : SimplexCategory) {m : ℕ}
    {t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n}
    {b : (Δ[m] : SSet.{u}) ⟶ (Δ[0] : SSet.{u})}
    (sq : CommSq t (boundary m).ι (JZeroProjection n) b) :
    (boundary m).ι ≫ (JBoundaryLift n sq).l = t :=
  (JBoundaryLift n sq).fac_left

/-- The same boundary lift retains the whole prescribed bottom map. -/
@[reassoc]
theorem JBoundaryLift_fac_right (n : SimplexCategory) {m : ℕ}
    {t : (boundary.{u} m : SSet.{u}) ⟶ J.obj n}
    {b : (Δ[m] : SSet.{u}) ⟶ (Δ[0] : SSet.{u})}
    (sq : CommSq t (boundary m).ι (JZeroProjection n) b) :
    (JBoundaryLift n sq).l ≫ JZeroProjection n = b :=
  (JBoundaryLift n sq).fac_right

/-- The actual full-J point projection has RLP against every original boundary. -/
theorem JZeroProjection_boundaryRLP (n : SimplexCategory) :
    modelCategoryQuillen.I.{u}.rlp (JZeroProjection n) := by
  intro A B i hi
  cases hi with
  | mk m =>
    exact ⟨fun sq => { exists_lift := ⟨JBoundaryLift n sq⟩ }⟩

/-- The constructed point projection is a genuine scalar Kan trivial fibration. -/
theorem JZeroProjection_trivialFibration (n : SimplexCategory) :
    trivialFibrations SSet.{u} (JZeroProjection n) := by
  rw [← cofibrations_rlp]
  change (monomorphisms SSet.{u}).rlp (JZeroProjection n)
  rw [SSet.rlp_monomorphisms]
  exact JZeroProjection_boundaryRLP n

/-- The same projection induces the fundamental-groupoid and every based π equivalence. -/
theorem JZeroProjection_KanComplexW (n : SimplexCategory) :
    KanComplex.W (JZeroProjection.{u} n) := by
  let _ : Fibration (JZeroProjection.{u} n) :=
    (HomotopicalAlgebra.fibration_iff _).2 (JZeroProjection_trivialFibration n).1
  let _ : KanComplex (J.{u}.obj n) :=
    (HomotopicalAlgebra.isFibrant_iff_of_isTerminal (JZeroProjection n)
      stdSimplex.isTerminalObj₀).2 inferInstance
  let _ : KanComplex (Δ[0] : SSet.{u}) :=
    (HomotopicalAlgebra.isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u}))
      stdSimplex.isTerminalObj₀).2 inferInstance
  exact (KanComplex.W_iff_realizationWeakEquivalence (JZeroProjection n)).mpr
    (JZeroProjection_trivialFibration n).2

/-- Every original cosimplicial map retains the same full-J point projection. -/
@[reassoc]
theorem JZeroProjection_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    J.{u}.map f ≫ JZeroProjection m = JZeroProjection n :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

private def ordinalLast (n : SimplexCategory) : ordinal.{u}.obj n :=
  ULift.up (Fin.last n.len)

private def ordinalLast_isTerminal (n : SimplexCategory) :
    IsTerminal (ordinalLast.{u} n) :=
  IsTerminal.ofUniqueHom
    (fun Y => by
      change ULift.{u} (Fin (n.len + 1)) at Y
      change Y ⟶ ULift.up (Fin.last n.len)
      exact homOfLE (by
        change Y.down ≤ Fin.last n.len
        exact Fin.le_last _))
    (fun Y f => by
      change ULift.{u} (Fin (n.len + 1)) at Y
      change (Y ⟶ ULift.up (Fin.last n.len)) at f
      apply ULift.ext
      apply PLift.ext
      exact Subsingleton.elim _ _)

private theorem stdSimplex_projection_weak (n : SimplexCategory) :
    realizationWeakEquivalences
      (stdSimplex.isTerminalObj₀.from (stdSimplex.{u}.obj n)) := by
  let e := ordinalNerveIso.{u}.app n
  have hN := NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal
    (ordinalLast_isTerminal.{u} n)
  have hIso : realizationWeakEquivalences e.hom :=
    (HomotopicalAlgebra.weakEquivalence_iff (C := SSet.{u}) e.hom).mp inferInstance
  have h := realizationWeakEquivalences.comp_mem e.hom _ hIso hN
  have he : e.hom ≫ stdSimplex.isTerminalObj₀.from (nerve (ordinal.{u}.obj n)) =
      stdSimplex.isTerminalObj₀.from (stdSimplex.{u}.obj n) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rwa [he] at h

/-- The original standard simplex inclusion into its full groupoid nerve is weak homotopy. -/
theorem simplexInclusion_realizationWeak (n : SimplexCategory) :
    realizationWeakEquivalences (simplexInclusion.{u}.app n) := by
  have hp : realizationWeakEquivalences (JZeroProjection.{u} n) :=
    (JZeroProjection_trivialFibration n).2
  apply realizationWeakEquivalences.of_postcomp (simplexInclusion.app n) (JZeroProjection n) hp
  have h : simplexInclusion.app n ≫ JZeroProjection n =
      stdSimplex.isTerminalObj₀.from (stdSimplex.{u}.obj n) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]
  exact stdSimplex_projection_weak n

/-- The same original k comparison is weak on every original representable. -/
theorem kComparison_representable_realizationWeak (n : SimplexCategory) :
    realizationWeakEquivalences (kComparison.{u}.app (stdSimplex.obj n)) := by
  have hIso : realizationWeakEquivalences (kRepresentableIso.{u}.hom.app n) :=
    (HomotopicalAlgebra.weakEquivalence_iff (C := SSet.{u})
      (kRepresentableIso.{u}.hom.app n)).mp inferInstance
  apply realizationWeakEquivalences.of_postcomp
    (kComparison.app (stdSimplex.obj n)) (kRepresentableIso.hom.app n) hIso
  rw [kComparison_representable]
  exact simplexInclusion_realizationWeak n

end SSet.FreeGroupoidSimplex
