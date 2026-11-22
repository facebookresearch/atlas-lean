/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteNerve
import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteKan
import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteFiniteProducts
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The genuine coherent-nerve finite row model

Every inner simplex is a full ordered matrix of coherent-interval vertices.
The chosen finite product, all outer reindexings and both contraction endpoints
are constructed on whole simplicial sets. Identification with the actual raw
closed-power diagonal is a separate required comparison, not a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SSet.RezkRawEFiniteRows
open CategoryTheory.Codiscrete

/-- The full row nerve: inner n-simplices are (n+1) ordered vectors of (k+1) vertices. -/
def rowNerve (k : ℕ) : SSet.{u} :=
  functorToSSet.obj (Fin (k + 1) → ULift.{u} Bool)

/-- The actual chosen finite product of the original coherent interval. -/
def rowProduct (k : ℕ) : SSet.{u} :=
  ∏ᶜ fun _ : Fin (k + 1) => coherentIso.{u}

/-- The finite-product Iso is the actual native comparison, including the chosen Type product. -/
def rowProductIso (k : ℕ) : rowNerve.{u} k ≅ rowProduct k :=
  ((functorToSSet : Type u ⥤ SSet.{u}).mapIso
    (Types.productIso (fun _ : Fin (k + 1) => ULift.{u} Bool))).symm ≪≫
    PreservesProduct.iso (functorToSSet : Type u ⥤ SSet.{u})
      (fun _ : Fin (k + 1) => ULift.{u} Bool)

/-- The same comparison retains its actual forward map. -/
def rowToProduct (k : ℕ) : rowNerve.{u} k ⟶ rowProduct k :=
  (rowProductIso k).hom

/-- The inverse is the genuine finite-product inverse, not a supplied inverse record. -/
def productToRow (k : ℕ) : rowProduct.{u} k ⟶ rowNerve k :=
  (rowProductIso k).inv

/-- Every product projection is the original vector coordinate. -/
theorem rowToProduct_π (k : ℕ) (i : Fin (k + 1)) :
    rowToProduct.{u} k ≫ Limits.Pi.π (fun _ : Fin (k + 1) => coherentIso.{u}) i =
      functorToSSet.map (↾fun f : Fin (k + 1) → ULift.{u} Bool => f i) := by
  change
    ((functorToSSet : Type u ⥤ SSet.{u}).map
        (Types.productIso (fun _ : Fin (k + 1) => ULift.{u} Bool)).inv ≫
      piComparison (functorToSSet : Type u ⥤ SSet.{u})
        (fun _ : Fin (k + 1) => ULift.{u} Bool)) ≫
      Limits.Pi.π (fun _ : Fin (k + 1) => functorToSSet.obj (ULift.{u} Bool)) i =
    functorToSSet.map (↾fun f : Fin (k + 1) → ULift.{u} Bool => f i)
  rw [Category.assoc, piComparison_comp_π, ← Functor.map_comp,
    Types.productIso_inv_comp_π]

/-- The inverse preserves the same coordinate without any definitional product substitution. -/
theorem productToRow_π (k : ℕ) (i : Fin (k + 1)) :
    productToRow.{u} k ≫
      functorToSSet.map (↾fun f : Fin (k + 1) → ULift.{u} Bool => f i) =
      Limits.Pi.π (fun _ : Fin (k + 1) => coherentIso.{u}) i := by
  change (rowProductIso k).inv ≫
      functorToSSet.map (↾fun f : Fin (k + 1) → ULift.{u} Bool => f i) =
    Limits.Pi.π (fun _ : Fin (k + 1) => coherentIso.{u}) i
  have h := rowToProduct_π k i
  change (rowProductIso k).hom ≫
      Limits.Pi.π (fun _ : Fin (k + 1) => coherentIso.{u}) i =
    functorToSSet.map (↾fun f : Fin (k + 1) → ULift.{u} Bool => f i) at h
  exact (Iso.inv_comp_eq (rowProductIso k)).2 h.symm

/-- Full simplex coordinates, before taking components or realization. -/
def rowCoordinates (k n : ℕ) :
    (rowNerve.{u} k).obj (op ⦋n⦌) ≃
      (Fin (n + 1) → Fin (k + 1) → ULift.{u} Bool) :=
  Codiscrete.equivFun

/-- Every original inner operator reindexes the full first coordinate. -/
theorem rowCoordinates_inner (k : ℕ) {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (x : (rowNerve.{u} k).obj (op ⦋m⦌)) :
    rowCoordinates k n ((rowNerve k).map θ.op x) =
      fun i => rowCoordinates k m x (θ i) := rfl

/-- All original outer operators act by their literal contravariant vector reindexing. -/
def rowMap {k l : SimplexCategoryᵒᵖ} (θ : k ⟶ l) :
    rowNerve.{u} k.unop.len ⟶ rowNerve l.unop.len :=
  functorToSSet.map (↾fun f => f ∘ θ.unop.toOrderHom)

/-- All inner and outer coordinates survive at once. -/
theorem rowMap_coordinates {k l : SimplexCategoryᵒᵖ} (θ : k ⟶ l)
    (n : ℕ) (x : (rowNerve.{u} k.unop.len).obj (op ⦋n⦌)) :
    rowCoordinates l.unop.len n ((rowMap θ).app (op ⦋n⦌) x) =
      fun i j => rowCoordinates k.unop.len n x i (θ.unop j) := rfl

/-- The chosen full vector is the actual all-false original E vertex. -/
def rowBase (k : ℕ) : (rowNerve.{u} k).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ (Codiscrete.mk (fun _ => ULift.up false))

/-- The contraction is the actual codiscrete product inverse followed by a total function. -/
def rowContraction (k : ℕ) : rowNerve.{u} k ⨯ coherentIso.{u} ⟶ rowNerve k :=
  (Codiscrete.prodIso (Fin (k + 1) → ULift.{u} Bool) (ULift.{u} Bool)).inv ≫
    functorToSSet.map (↾fun (p : (Fin (k + 1) → ULift.{u} Bool) × ULift.{u} Bool) =>
      if p.2.down then p.1 else fun _ => ULift.up false)

private theorem rowContraction_vertex (k : ℕ) (d : SimplexCategoryᵒᵖ)
    (x : (rowNerve.{u} k ⨯ coherentIso.{u}).obj d) (j : Fin (d.unop.len + 1)) :
    (((rowContraction k).app d x).obj j).as =
      if (((prod.snd (X := rowNerve.{u} k) (Y := coherentIso.{u})).app d x).obj j).as.down then
        (((prod.fst (X := rowNerve.{u} k) (Y := coherentIso.{u})).app d x).obj j).as
      else fun _ => ULift.up false := rfl

/-- Both original coherent E endpoints are whole maps, not vertex bijections. -/
theorem rowContraction_endpoints (k : ℕ) :
    prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₀) ≫ rowContraction k =
      SSet.const (rowBase k) ∧
    prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₁) ≫ rowContraction k =
      𝟙 (rowNerve k) := by
  constructor
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply CategoryTheory.nerve.ext_of_isThin
      (C := Codiscrete (Fin (k + 1) → ULift.{u} Bool))
    funext j
    apply Codiscrete.ext
    change (((rowContraction k).app d
      ((prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₀)).app d x)).obj j).as =
        (((SSet.const (X := rowNerve.{u} k) (rowBase k)).app d x).obj j).as
    rw [rowContraction_vertex]
    have hfst :
        (prod.fst (X := rowNerve.{u} k) (Y := coherentIso.{u})).app d
          ((prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₀)).app d x) =
        x :=
      congrArg (fun h : rowNerve.{u} k ⟶ rowNerve k => h.app d x)
        (prod.lift_fst (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₀))
    have hsnd :
        (prod.snd (X := rowNerve.{u} k) (Y := coherentIso.{u})).app d
          ((prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₀)).app d x) =
        (SSet.const (X := rowNerve.{u} k) coherentIso.x₀).app d x :=
      congrArg (fun h : rowNerve.{u} k ⟶ coherentIso.{u} => h.app d x)
        (prod.lift_snd (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₀))
    rw [hfst, hsnd]
    rfl
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply CategoryTheory.nerve.ext_of_isThin
      (C := Codiscrete (Fin (k + 1) → ULift.{u} Bool))
    funext j
    apply Codiscrete.ext
    change (((rowContraction k).app d
      ((prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₁)).app d x)).obj j).as =
        (x.obj j).as
    rw [rowContraction_vertex]
    have hfst :
        (prod.fst (X := rowNerve.{u} k) (Y := coherentIso.{u})).app d
          ((prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₁)).app d x) =
        x :=
      congrArg (fun h : rowNerve.{u} k ⟶ rowNerve k => h.app d x)
        (prod.lift_fst (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₁))
    have hsnd :
        (prod.snd (X := rowNerve.{u} k) (Y := coherentIso.{u})).app d
          ((prod.lift (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₁)).app d x) =
        (SSet.const (X := rowNerve.{u} k) coherentIso.x₁).app d x :=
      congrArg (fun h : rowNerve.{u} k ⟶ coherentIso.{u} => h.app d x)
        (prod.lift_snd (𝟙 (rowNerve.{u} k)) (SSet.const coherentIso.x₁))
    rw [hfst, hsnd]
    rfl

/-- The same contraction is natural for every original outer operator. -/
theorem rowContraction_outer {k l : SimplexCategoryᵒᵖ} (θ : k ⟶ l) :
    prod.map (rowMap θ) (𝟙 coherentIso.{u}) ≫ rowContraction l.unop.len =
      rowContraction k.unop.len ≫ rowMap θ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.nerve.ext_of_isThin
    (C := Codiscrete (Fin (l.unop.len + 1) → ULift.{u} Bool))
  funext j
  apply Codiscrete.ext
  change (((rowContraction l.unop.len).app d
      ((prod.map (rowMap θ) (𝟙 coherentIso.{u})).app d x)).obj j).as =
    (((rowMap θ).app d ((rowContraction k.unop.len).app d x)).obj j).as
  rw [rowContraction_vertex]
  have hfst :
      (prod.fst (X := rowNerve.{u} l.unop.len) (Y := coherentIso.{u})).app d
        ((prod.map (rowMap θ) (𝟙 coherentIso.{u})).app d x) =
      (rowMap θ).app d
        ((prod.fst (X := rowNerve.{u} k.unop.len) (Y := coherentIso.{u})).app d x) :=
    congrArg (fun h : rowNerve.{u} k.unop.len ⨯ coherentIso.{u} ⟶ rowNerve l.unop.len => h.app d x)
      (prod.map_fst (rowMap θ) (𝟙 coherentIso.{u}))
  have hsnd :
      (prod.snd (X := rowNerve.{u} l.unop.len) (Y := coherentIso.{u})).app d
        ((prod.map (rowMap θ) (𝟙 coherentIso.{u})).app d x) =
      (prod.snd (X := rowNerve.{u} k.unop.len) (Y := coherentIso.{u})).app d x :=
    congrArg (fun h : rowNerve.{u} k.unop.len ⨯ coherentIso.{u} ⟶ coherentIso.{u} => h.app d x)
      ((prod.map_snd (rowMap θ) (𝟙 coherentIso.{u})).trans (Category.comp_id _))
  rw [hfst, hsnd]
  change
    (if
        (((prod.snd (X := rowNerve.{u} k.unop.len) (Y := coherentIso.{u})).app d x).obj
          j).as.down then
      (((prod.fst (X := rowNerve.{u} k.unop.len) (Y := coherentIso.{u})).app d x).obj j).as ∘
          θ.unop.toOrderHom
    else fun _ => ULift.up false) =
      (((rowContraction k.unop.len).app d x).obj j).as ∘ θ.unop.toOrderHom
  rw [rowContraction_vertex]
  cases
      (((prod.snd (X := rowNerve.{u} k.unop.len) (Y := coherentIso.{u})).app d x).obj
        j).as.down <;> rfl

/-- Kan structure is derived from the genuine codiscrete nerve theorem in every outer row. -/
theorem rowNerve_kan (k : ℕ) : SSet.KanComplex (rowNerve.{u} k) :=
  Codiscrete.kanComplex_functorToSSet_obj _

/-- The terminal map is weak through the explicit initial object of the actual codiscrete nerve. -/
theorem rowNerve_terminal_weak (k : ℕ) :
    SSet.realizationWeakEquivalences (terminal.from (rowNerve.{u} k)) := by
  let a : Codiscrete (Fin (k + 1) → ULift.{u} Bool) :=
    Codiscrete.mk (fun _ => ULift.up false)
  have ha : IsInitial a := (isInitialEquivUnique _ a).symm (fun _ => inferInstance)
  exact NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial ha


end SSet.RezkRawEFiniteRows
