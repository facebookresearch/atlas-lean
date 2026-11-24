/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FreeComputad
public import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategory

/-!
# Strict representation of the original simplicial computad

An interpretation consists of the actual object function and the images
of atomic arrows, with their original scalar equations. The native free
category constructs the entire strict enriched functor. Conversely,
reading a strict functor recovers those primitive fields; both entire
round trips are proved.
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory

namespace SSet.SimplicialComputad

variable {O : Type w} {C : Type v} [EnrichedCategory SSet.{max u w} C]
  {G H : O → O → Type u}

/-- Evaluate original paths by the native free-category functor into the scalar category. -/
def evaluate (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ) {x y : O} :
    Path G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ :=
  let φ : Vertex G ⥤q ScalarObject C Δ :=
    { obj := fun x => ⟨a x.label⟩
      map := g }
  (Paths.lift φ).map

/-- The original identity path is interpreted as the native enriched identity. -/
theorem evaluate_nil (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ) (x : O) :
    evaluate a Δ g (Quiver.Path.nil : Path G x x) =
      (eId SSet.{max u w} (a x)).app Δ PUnit.unit := rfl

/-- Interpreting a cons uses the original enriched composition. -/
theorem evaluate_cons (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ) {x y z : O}
    (p : Path G x y) (e : G y z) :
    evaluate a Δ g (p.cons e) =
      (eComp SSet.{max u w} (a x) (a y) (a z)).app Δ ⟨evaluate a Δ g p, g e⟩ := rfl

/-- Interpreting a singleton recovers its prescribed atomic value. -/
theorem evaluate_single (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ) {x y : O} (e : G x y) :
    evaluate a Δ g (single e) = g e := by
  let φ : Vertex G ⥤q ScalarObject C Δ :=
    { obj := fun x => ⟨a x.label⟩
      map := g }
  exact Paths.lift_toPath φ e

/-- Interpretation preserves the actual full path composition. -/
theorem evaluate_comp (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ) {x y z : O}
    (p : Path G x y) (q : Path G y z) :
    evaluate a Δ g (p.comp q) =
      (eComp SSet.{max u w} (a x) (a y) (a z)).app Δ ⟨evaluate a Δ g p, evaluate a Δ g q⟩ := by
  let φ : Vertex G ⥤q ScalarObject C Δ :=
    { obj := fun x => ⟨a x.label⟩
      map := g }
  exact (Paths.lift φ).map_comp p q

/-- Atomic equality determines equality of the complete path interpretations. -/
theorem evaluate_congr (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g h : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ)
    (e : ∀ {x y} (p : G x y), g p = h p) {x y : O} (p : Path G x y) :
    evaluate a Δ g p = evaluate a Δ h p := by
  suffices hh : ∀ {x y : Vertex G} (p : Quiver.Path x y),
      evaluate a Δ g p = evaluate a Δ h p from hh p
  intro x y p
  induction p with
  | nil => rfl
  | cons p f ih => rw [evaluate_cons, evaluate_cons, ih, e]

/-- Interpreting a free extension evaluates each of its original path images. -/
theorem evaluate_pathMap (a : O → C) (Δ : SimplexCategoryᵒᵖ)
    (g : ∀ {x y}, H x y → (a x ⟶[SSet.{max u w}] a y).obj Δ)
    (f : ∀ {x y}, G x y → Path H x y) {x y : O} (p : Path G x y) :
    evaluate a Δ g (pathMap f p) =
      evaluate a Δ (fun e => evaluate a Δ g (f e)) p := by
  suffices hh : ∀ {x y : Vertex G} (p : Quiver.Path x y),
      evaluate a Δ g (pathMap f p) =
        evaluate a Δ (fun e => evaluate a Δ g (f e)) p from hh p
  intro x y p
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [pathMap_cons, evaluate_comp, ih, evaluate_cons]

/-- Original scalar operators commute with the whole interpretation of paths. -/
theorem evaluate_scalar (a : O → C) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (g : ∀ {x y}, G x y → (a x ⟶[SSet.{max u w}] a y).obj Δ) {x y : O} (p : Path G x y) :
    (a x ⟶[SSet.{max u w}] a y).map θ (evaluate a Δ g p) =
      evaluate a Δ' (fun {x y} e => (a x ⟶[SSet.{max u w}] a y).map θ (g e)) p := by
  suffices hh : ∀ {x y : Vertex G} (p : Quiver.Path x y),
      (a x.label ⟶[SSet.{max u w}] a y.label).map θ (evaluate a Δ g p) =
        evaluate a Δ' (fun {x y} e => (a x ⟶[SSet.{max u w}] a y).map θ (g e)) p from hh p
  intro x y p
  induction p with
  | nil => exact (scalarOperator (C := C) θ).map_id ⟨a x.label⟩
  | @cons y z p e ih =>
    rw [evaluate_cons, evaluate_cons]
    have h := (scalarOperator (C := C) θ).map_comp
      (X := ⟨a x.label⟩) (Y := ⟨a y.label⟩) (Z := ⟨a z.label⟩)
      (evaluate a Δ g p) (g e)
    exact h.trans (congrArg
      (fun q => (eComp SSet.{max u w} (a x.label) (a y.label) (a z.label)).app Δ'
        ⟨q, (a y.label ⟶[SSet.{max u w}] a z.label).map θ (g e)⟩) ih)

variable (A : SimplicialComputad.{u, w} O)

/-- The original primitive interpretation, with no assumed strict-functor extension. -/
@[ext]
structure Assignment where
  /-- The original object function. -/
  obj : O → C
  /-- The original images of all atomic arrows. -/
  atom (Δ : SimplexCategoryᵒᵖ) {x y : O} :
    A.generator Δ x y → (obj x ⟶[SSet.{max u w}] obj y).obj Δ
  /-- Scalar faces and degeneracies use their actual, possibly composite, path images. -/
  operator {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') {x y : O} (g : A.generator Δ x y) :
    (obj x ⟶[SSet.{max u w}] obj y).map θ (atom Δ g) =
      evaluate obj Δ' (atom Δ') (A.operator θ g)

/-- All scalar equations of a primitive interpretation hold on complete paths. -/
theorem Assignment.map_natural (d : Assignment A (C := C))
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') {x y : O}
    (p : Path (A.generator Δ) x y) :
    (d.obj x ⟶[SSet.{max u w}] d.obj y).map θ (evaluate d.obj Δ (d.atom Δ) p) =
      evaluate d.obj Δ' (d.atom Δ') (A.map θ p) := by
  exact (evaluate_scalar d.obj θ (d.atom Δ) p).trans
    ((evaluate_congr d.obj Δ' _ _ (fun g => d.operator θ g) p).trans
      (evaluate_pathMap d.obj Δ' (d.atom Δ') (A.operator θ) p).symm)

/-- The native free-category construction gives the entire strict enriched interpretation. -/
def Assignment.toFunctor (d : Assignment A (C := C)) : EnrichedFunctor SSet.{max u w}
  A.Object C where
  obj x := d.obj x.label
  map x y :=
    { app Δ := ↾evaluate d.obj Δ (d.atom Δ)
      naturality := by
        intro Δ Δ' θ
        ext p
        exact (d.map_natural A θ p).symm }
  map_id x := by
    ext Δ p
    rfl
  map_comp x y z := by
    ext Δ p
    exact evaluate_comp d.obj Δ (d.atom Δ) p.1 p.2

/-- A strict enriched functor is exactly the native free evaluation of its original atomic
images. -/
theorem functor_map_path (F : EnrichedFunctor SSet.{max u w} A.Object C)
    (Δ : SimplexCategoryᵒᵖ) {x y : O} (p : Path (A.generator Δ) x y) :
    (F.map ⟨x⟩ ⟨y⟩).app Δ p =
      evaluate (fun x => F.obj ⟨x⟩) Δ
        (fun {x y} g => (F.map ⟨x⟩ ⟨y⟩).app Δ (single g)) p := by
  suffices h : ∀ {x y : Vertex (A.generator Δ)} (p : Quiver.Path x y),
      (F.map ⟨x.label⟩ ⟨y.label⟩).app Δ p =
        evaluate (fun x => F.obj ⟨x⟩) Δ
          (fun {x y} g => (F.map ⟨x⟩ ⟨y⟩).app Δ (single g)) p from h p
  intro x y p
  induction p with
  | nil => exact congrArg (fun q => q.app Δ PUnit.unit) (F.map_id ⟨x.label⟩)
  | @cons y z p g ih =>
    rw [evaluate_cons]
    have h := congrArg (fun q => q.app Δ ⟨p, single g⟩)
      (F.map_comp ⟨x.label⟩ ⟨y.label⟩ ⟨z.label⟩)
    exact h.trans (congrArg
      (fun q => (eComp SSet.{max u w} (F.obj ⟨x.label⟩) (F.obj ⟨y.label⟩) (F.obj ⟨z.label⟩)).app Δ
        ⟨q, (F.map ⟨y.label⟩ ⟨z.label⟩).app Δ (single g)⟩) ih)

/-- Read the actual object function and every atomic image of a strict enriched functor. -/
def readback (F : EnrichedFunctor SSet.{max u w} A.Object C) : Assignment A (C := C) where
  obj x := F.obj ⟨x⟩
  atom Δ {x y} g := (F.map ⟨x⟩ ⟨y⟩).app Δ (single g)
  operator {Δ Δ'} θ {x y} g := by
    calc
      (F.obj ⟨x⟩ ⟶[SSet.{max u w}] F.obj ⟨y⟩).map θ ((F.map ⟨x⟩ ⟨y⟩).app Δ (single g)) =
          (F.map ⟨x⟩ ⟨y⟩).app Δ' (A.map θ (single g)) :=
        (NatTrans.naturality_apply (F.map ⟨x⟩ ⟨y⟩) θ (single g)).symm
      _ = (F.map ⟨x⟩ ⟨y⟩).app Δ' (A.operator θ g) :=
        congrArg ((F.map ⟨x⟩ ⟨y⟩).app Δ') (pathMap_single (A.operator θ) g)
      _ = evaluate (fun x => F.obj ⟨x⟩) Δ'
          (fun {x y} e => (F.map ⟨x⟩ ⟨y⟩).app Δ' (single e)) (A.operator θ g) :=
        functor_map_path A F Δ' (A.operator θ g)

/-- The reconstruction retains the entire original strict enriched functor. -/
theorem toFunctor_readback (F : EnrichedFunctor SSet.{max u w} A.Object C) :
    (readback A F).toFunctor A = F := by
  refine EnrichedFunctor.ext SSet.{max u w} (F := (readback A F).toFunctor A) (G := F)
    (fun x => rfl) ?_
  intro x y
  ext Δ p
  exact (functor_map_path A F Δ p).symm

/-- Reading the reconstructed functor retains every original primitive field. -/
theorem readback_toFunctor (d : Assignment A (C := C)) :
    readback A (d.toFunctor A) = d := by
  apply Assignment.ext
  · rfl
  · apply heq_of_eq
    funext Δ x y g
    exact evaluate_single d.obj Δ (d.atom Δ) g

/-- The strict functors and their actual primitive interpretations are genuinely equivalent. -/
def functorEquiv : (EnrichedFunctor SSet.{max u w} A.Object C) ≃ Assignment A (C := C) where
  toFun := readback A
  invFun := Assignment.toFunctor A
  left_inv := toFunctor_readback A
  right_inv := readback_toFunctor A

end SSet.SimplicialComputad
