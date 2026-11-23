/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationHomotopyExtension
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCertificates
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeRegularPathCoefficients
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Homotopy lifting through simplicial covers

A homotopy in the base of a simplicial fibration lifts from its given initial
map. For the fundamental-groupoid cover of a Kan complex, maps over the base are
determined by the identity point. An identity-base self-homotopy lifts from the
cover identity to a map over the base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet

/-- Lift an actual base homotopy through a fibration from its original endpoint-zero map. -/
theorem exists_homotopy_lift₀ {A E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (f : A ⟶ E) {g : A ⟶ B} (H : Homotopy (f ≫ p) g) :
    ∃ psi : A ⊗ (Δ[1] : SSet.{u}) ⟶ E,
      ι₀ ≫ psi = f ∧ psi ≫ p = H.h := by
  let K : SSet.{u} := (⊥ : A.Subcomplex)
  let i : K ⟶ A := (⊥ : A.Subcomplex).ι
  let hK : IsInitial K := Subcomplex.isInitialBot
  let e : K ⊗ (Δ[1] : SSet.{u}) ≅ K :=
    CategoryTheory.mulZero (A := (Δ[1] : SSet.{u})) hK
  let hKI : IsInitial (K ⊗ (Δ[1] : SSet.{u})) := hK.ofIso e.symm
  let top : K ⊗ (Δ[1] : SSet.{u}) ⟶ E := hKI.to E
  obtain ⟨psi, hZero, _, hProjection⟩ := homotopy_extension_property₀ i p top f
    (hK.hom_ext _ _) H.h H.h₀ (hKI.hom_ext _ _)
  exact ⟨psi, hZero, hProjection⟩

namespace KanComplex

private def firstVertexInclusion (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))

private theorem firstVertexInclusion_one : firstVertexInclusion.{u} 1 =
    SSet.stdSimplex.δ (1 : Fin 2) := by
  change SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    SSet.stdSimplex.δ (1 : Fin 2)
  exact (SSet.yonedaEquiv_symm_zero _).trans SSet.stdSimplex.δ_one_eq_const.symm

private theorem nativeLift_eq_of_firstVertex {Y : SSet.{u}} (y : Y _⦋0⦌) {n : ℕ}
    (f g : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y)
    (hProjection : f ≫ nativeCoverProjection Y y = g ≫ nativeCoverProjection Y y)
    (hFirst : firstVertexInclusion n ≫ f = firstVertexInclusion n ≫ g) : f = g := by
  let sigma := f ≫ nativeCoverProjection Y y
  let Lf : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y //
      L ≫ nativeCoverProjection Y y = sigma} := ⟨f, rfl⟩
  let Lg : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover Y y //
      L ≫ nativeCoverProjection Y y = sigma} := ⟨g, hProjection.symm⟩
  let E := nativeCoverSimplexFiberVertexEquiv (X := Y) (x := y) sigma
  have hValue : (E Lf).val = (E Lg).val :=
    (nativeCoverSimplexFiberVertexEquiv_apply sigma Lf).trans
      ((congrArg (SSet.yonedaEquiv (X := nativeCover Y y) (n := ⦋0⦌)) hFirst).trans
        (nativeCoverSimplexFiberVertexEquiv_apply sigma Lg).symm)
  exact congrArg Subtype.val (E.injective (Subtype.ext hValue))

/-- Original maps between native covers over the same base are determined by the original identity
point. -/
theorem nativeCover_map_ext_at_identity {X Y : SSet.{u}} [SSet.KanComplex X]
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f g : nativeCover X x ⟶ nativeCover Y y)
    (hProjection : f ≫ nativeCoverProjection Y y = g ≫ nativeCoverProjection Y y)
    (hPoint : f.app (Opposite.op ⦋0⦌) (nativeCoverIdentityPoint X x) =
      g.app (Opposite.op ⦋0⦌) (nativeCoverIdentityPoint X x)) : f = g := by
  let P := nativeCover X x
  let Q := nativeCover Y y
  let p := nativeCoverProjection Y y
  let b := nativeCoverIdentityPoint X x
  have hVertices (v : P _⦋0⦌) : f.app (Opposite.op ⦋0⦌) v = g.app (Opposite.op ⦋0⦌) v := by
    obtain ⟨e⟩ := nativeCover_exists_edge_from_identityPoint (X := X) (x := x) v
    let a : (Δ[1] : SSet.{u}) ⟶ P := SSet.yonedaEquiv.symm e.edge
    have hBase : (a ≫ f) ≫ p = (a ≫ g) ≫ p :=
      (Category.assoc a f p).trans
        ((congrArg (fun k => a ≫ k) hProjection).trans (Category.assoc a g p).symm)
    have hStart : firstVertexInclusion 1 ≫ a = SSet.const b :=
      (congrArg (fun k => k ≫ a) firstVertexInclusion_one).trans
        ((SSet.Edge.δ_one_yonedaEquiv_symm e).trans (SSet.yonedaEquiv_symm_zero b))
    have hFirst : firstVertexInclusion 1 ≫ (a ≫ f) = firstVertexInclusion 1 ≫ (a ≫ g) :=
      (Category.assoc (firstVertexInclusion 1) a f).symm.trans
        ((congrArg (fun k => k ≫ f) hStart).trans
          ((SSet.const_comp b f).trans
            ((congrArg (fun z => (SSet.const z : (Δ[0] : SSet.{u}) ⟶ Q)) hPoint).trans
              ((SSet.const_comp b g).symm.trans
                ((congrArg (fun k => k ≫ g) hStart.symm).trans
                  (Category.assoc (firstVertexInclusion 1) a g))))))
    have hLift : a ≫ f = a ≫ g := nativeLift_eq_of_firstVertex y _ _ hBase hFirst
    have hEnd : SSet.stdSimplex.δ (0 : Fin 2) ≫ a = SSet.const v :=
      (SSet.Edge.δ_zero_yonedaEquiv_symm e).trans (SSet.yonedaEquiv_symm_zero v)
    have hZero : SSet.const (f.app (Opposite.op ⦋0⦌) v) =
        (SSet.const (g.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ Q) :=
      (SSet.const_comp v f).symm.trans
        ((congrArg (fun k => k ≫ f) hEnd.symm).trans
          ((Category.assoc (SSet.stdSimplex.δ (0 : Fin 2)) a f).trans
            ((congrArg (fun k => SSet.stdSimplex.δ (0 : Fin 2) ≫ k) hLift).trans
              ((Category.assoc (SSet.stdSimplex.δ (0 : Fin 2)) a g).symm.trans
                ((congrArg (fun k => k ≫ g) hEnd).trans (SSet.const_comp v g))))))
    exact (SSet.yonedaEquiv_const (f.app (Opposite.op ⦋0⦌) v)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := Q) (n := ⦋0⦌)) hZero).trans
        (SSet.yonedaEquiv_const (g.app (Opposite.op ⦋0⦌) v)))
  have hSimplex (n : ℕ) (a : (Δ[n] : SSet.{u}) ⟶ P) : a ≫ f = a ≫ g := by
    let v := SSet.yonedaEquiv (firstVertexInclusion n ≫ a)
    have hFirstSource : firstVertexInclusion n ≫ a = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) :=
      ((SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm_apply_apply
        (firstVertexInclusion n ≫ a)).symm.trans (SSet.yonedaEquiv_symm_zero v)
    have hBase : (a ≫ f) ≫ p = (a ≫ g) ≫ p :=
      (Category.assoc a f p).trans
        ((congrArg (fun k => a ≫ k) hProjection).trans (Category.assoc a g p).symm)
    have hFirst : firstVertexInclusion n ≫ (a ≫ f) = firstVertexInclusion n ≫ (a ≫ g) :=
      (Category.assoc (firstVertexInclusion n) a f).symm.trans
        ((congrArg (fun k => k ≫ f) hFirstSource).trans
          ((SSet.const_comp v f).trans
            ((congrArg (fun z => (SSet.const z : (Δ[0] : SSet.{u}) ⟶ Q)) (hVertices v)).trans
              ((SSet.const_comp v g).symm.trans
                ((congrArg (fun k => k ≫ g) hFirstSource.symm).trans
                  (Category.assoc (firstVertexInclusion n) a g))))))
    exact nativeLift_eq_of_firstVertex y _ _ hBase hFirst
  apply NatTrans.ext
  funext d
  rcases d with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  let a : (Δ[n] : SSet.{u}) ⟶ P := SSet.yonedaEquiv.symm s
  have h := congrArg (SSet.yonedaEquiv (X := Q) (n := ⦋n⦌)) (hSimplex n a)
  simpa only [SSet.yonedaEquiv_comp, a, Equiv.apply_symm_apply] using h

/-- An actual original identity self-homotopy lifts from identity on the SAME native cover. -/
theorem exists_nativeCover_selfHomotopy_lift {X : SSet.{u}} (x : X _⦋0⦌)
    (H : Homotopy (𝟙 X) (𝟙 X)) :
    ∃ f : nativeCover X x ⟶ nativeCover X x,
      ∃ K : Homotopy (𝟙 (nativeCover X x)) f,
        K.h ≫ nativeCoverProjection X x =
          (nativeCoverProjection X x ▷ (Δ[1] : SSet.{u})) ≫ H.h ∧
        f ≫ nativeCoverProjection X x = nativeCoverProjection X x := by
  let P := nativeCover X x
  let p := nativeCoverProjection X x
  let : Fibration p := nativeCoverProjection_fibration X x
  let T := (p ▷ (Δ[1] : SSet.{u})) ≫ H.h
  have hZeroBase : ι₀ ≫ T = (𝟙 P) ≫ p := by
    dsimp only [T]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀,
      Category.comp_id, Category.id_comp]
  have hOneBase : ι₁ ≫ T = p := by
    dsimp only [T]
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁, Category.comp_id]
  let h : Homotopy ((𝟙 P) ≫ p) p := Homotopy.mkOfH T hZeroBase hOneBase
  obtain ⟨psi, hZero, hProjection⟩ := exists_homotopy_lift₀ p (𝟙 P) h
  let f : P ⟶ P := ι₁ ≫ psi
  let K : Homotopy (𝟙 P) f := Homotopy.mkOfH psi hZero rfl
  have hCylinder : K.h ≫ p = (p ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
    rw [Homotopy.mkOfH_h]
    exact hProjection.trans (Homotopy.mkOfH_h T hZeroBase hOneBase)
  have hEnd : f ≫ p = p :=
    (Category.assoc ι₁ psi p).trans
      ((congrArg (fun q => ι₁ ≫ q) hProjection).trans h.h₁)
  exact ⟨f, K, hCylinder, hEnd⟩

end KanComplex
end SSet
