/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.CategoryTheory.Conj

/-!
# Fundamental groupoids and the first homotopy groups of Kan complexes

This file relates connected components and loop morphisms in the fundamental
groupoid of a Kan complex to `π₀` and the pointed homotopy groups `π 0` and
`π 1`.  It gives the resulting criterion for a map of Kan complexes to induce
an equivalence of fundamental groupoids, and repackages `KanComplex.W` in
terms of bijectivity on `π₀` and every positive homotopy group.

The mathematics follows the comparison used in Joël Riou's
`topcat-model-category` development, adapted independently to the current
fundamental-groupoid and homotopy-group APIs.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

namespace KanComplex

section PiZero

variable [KanComplex X]

/-- For a Kan complex, connected components agree with the zeroth pointed
homotopy group at any basepoint. -/
noncomputable def π₀EquivπZero (x : X _⦋0⦌) : π₀ X ≃ π 0 X x where
  toFun := π₀.lift (fun a ↦ π.mk ((PtSimplex.equiv₀ x).symm a)) (fun _ _ e ↦ by
    rw [π.mk_eq_mk_iff]
    exact ⟨PtSimplex.RelStruct₀.equiv₀.symm
      (e.inv.ofEq (by simp) (by simp))⟩)
  invFun := Quot.lift (fun p ↦ π₀.mk (PtSimplex.equiv₀ x p)) (fun _ _ ⟨h⟩ ↦
    π₀.sound (PtSimplex.Homotopy.equiv₀ h))
  left_inv a := by
    obtain ⟨a, rfl⟩ := a.mk_surjective
    exact congrArg π₀.mk ((PtSimplex.equiv₀ x).apply_symm_apply a)
  right_inv p := by
    obtain ⟨p, rfl⟩ := p.mk_surjective
    exact congrArg π.mk ((PtSimplex.equiv₀ x).symm_apply_apply p)

@[simp]
lemma π₀EquivπZero_mk (x a : X _⦋0⦌) :
    π₀EquivπZero x (π₀.mk a) = π.mk ((PtSimplex.equiv₀ x).symm a) :=
  rfl

lemma mapπ_comp_π₀EquivπZero
    (f : X ⟶ Y) [KanComplex Y] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : f.app _ x = y) :
    π.map f h 0 ∘ π₀EquivπZero x =
      π₀EquivπZero y ∘ mapπ₀ f := by
  funext a
  obtain ⟨a, rfl⟩ := a.mk_surjective
  apply congrArg π.mk
  apply (PtSimplex.equiv₀ y).injective
  change yonedaEquiv (yonedaEquiv.symm a ≫ f) = _
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact ((PtSimplex.equiv₀ y).apply_symm_apply _).symm

lemma bijective_mapπ₀_iff_bijective_mapπ_zero
    (f : X ⟶ Y) [KanComplex Y] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : f.app _ x = y) :
    Function.Bijective (π.map f h 0) ↔ Function.Bijective (mapπ₀ f) := by
  rw [← Function.Bijective.of_comp_iff _ (π₀EquivπZero x).bijective]
  rw [← Function.Bijective.of_comp_iff' (π₀EquivπZero y).bijective]
  rw [mapπ_comp_π₀EquivπZero]

end PiZero

end KanComplex

namespace FundamentalGroupoid

private def toπ₀ (z : FundamentalGroupoid X) : π₀ X := π₀.mk z.pt

@[simp]
private lemma toπ₀_mk (x : X _⦋0⦌) : toπ₀ (.mk x) = .mk x := rfl

variable [KanComplex X]

private lemma congr_toπ₀_of_hom {x y : FundamentalGroupoid X} (φ : x ⟶ y) :
    toπ₀ x = toπ₀ y := by
  obtain ⟨e, rfl⟩ := homMk_surjective φ
  exact π₀.sound e

private lemma toπ₀_eq_toπ₀_iff (x y : FundamentalGroupoid X) :
    toπ₀ x = toπ₀ y ↔ Nonempty (x ≅ y) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := mk_surjective x
    obtain ⟨y, rfl⟩ := mk_surjective y
    rw [toπ₀_mk, toπ₀_mk, π₀.mk_eq_mk_iff] at h
    induction h with
    | rel x y h =>
        obtain ⟨e⟩ := h
        exact ⟨asIso (homMk e)⟩
    | refl => exact ⟨Iso.refl _⟩
    | symm _ _ _ e => exact ⟨e.some.symm⟩
    | trans _ _ _ _ _ e₁ e₂ => exact ⟨e₁.some.trans e₂.some⟩
  · rintro ⟨e⟩
    exact congr_toπ₀_of_hom e.hom

private lemma π₀_mk_eq_π₀_mk_iff (x y : X _⦋0⦌) :
    π₀.mk x = π₀.mk y ↔ Nonempty (mk x ≅ mk y) :=
  toπ₀_eq_toπ₀_iff _ _

section Map

variable (f : X ⟶ Y) [KanComplex Y]

omit [KanComplex X] in
private lemma mapπ₀_surjective_iff :
    Function.Surjective (mapπ₀ f) ↔ (mapFundamentalGroupoid f).EssSurj := by
  constructor
  · intro hf
    constructor
    intro y
    obtain ⟨a, ha⟩ := hf (π₀.mk y.pt)
    obtain ⟨x, rfl⟩ := a.mk_surjective
    exact ⟨.mk x, (toπ₀_eq_toπ₀_iff _ _).mp ha⟩
  · intro h y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨z, ⟨e⟩⟩ := h.mem_essImage (.mk y)
    obtain ⟨x, rfl⟩ := mk_surjective z
    refine ⟨π₀.mk x, ?_⟩
    rw [mapπ₀_mk]
    exact (π₀_mk_eq_π₀_mk_iff _ _).mpr
      ⟨by simpa only [mapFundamentalGroupoid_obj_mk] using e⟩

private lemma mapπ₀_injective_iff :
    Function.Injective (mapπ₀ f) ↔
      (∀ (x x' : SSet.FundamentalGroupoid X),
        Nonempty ((mapFundamentalGroupoid f).obj x ≅ (mapFundamentalGroupoid f).obj x') →
          Nonempty (x ≅ x')) := by
  constructor
  · rintro hf x x' ⟨e⟩
    rw [← toπ₀_eq_toπ₀_iff]
    obtain ⟨x, rfl⟩ := mk_surjective x
    obtain ⟨x', rfl⟩ := mk_surjective x'
    apply hf
    change mapπ₀ f (π₀.mk x) = mapπ₀ f (π₀.mk x')
    rw [mapπ₀_mk, mapπ₀_mk, π₀_mk_eq_π₀_mk_iff]
    exact ⟨e⟩
  · intro hf a a' h
    obtain ⟨a, rfl⟩ := a.mk_surjective
    obtain ⟨a', rfl⟩ := a'.mk_surjective
    rw [mapπ₀_mk, mapπ₀_mk, π₀_mk_eq_π₀_mk_iff] at h
    rw [π₀_mk_eq_π₀_mk_iff]
    exact hf _ _ h

end Map

end FundamentalGroupoid

namespace KanComplex

open _root_.SSet.FundamentalGroupoid

section PiOneComparison

variable [KanComplex X]

end PiOneComparison

end KanComplex

end SSet

end

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

namespace KanComplex

open _root_.SSet.FundamentalGroupoid

section PiOneComparison

variable [KanComplex X]

private def edgePtEquiv {x : X _⦋0⦌} :
    Edge x x ≃ X.PtSimplex 1 x where
  toFun e :=
    { map := yonedaEquiv.symm e.edge
      comm := by
        apply boundary.hom_ext
        intro i
        fin_cases i <;>
          simp [boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm] }
  invFun p := Edge.mk (yonedaEquiv (RelativeMorphism.map p))
    (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
    (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
  left_inv e := by ext; simp
  right_inv p := by ext; simp

private def relStruct₀OfHomotopyR {x : X _⦋0⦌}
    {e e' : Edge x x} (h : Edge.HomotopyR e e') :
    (edgePtEquiv e).RelStruct₀ (edgePtEquiv e') where
  map := yonedaEquiv.symm h.simplex
  δ_castSucc_map := by
    apply yonedaEquiv.injective
    simp [edgePtEquiv]
  δ_succ_map := by
    apply yonedaEquiv.injective
    simp [edgePtEquiv]
  δ_map_of_lt j hj := by grind
  δ_map_of_gt j hj := by
    fin_cases j
    · simp at hj
    · simp at hj
    · apply yonedaEquiv.injective
      simp only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      calc
        _ = (Edge.id x).edge := by simp
        _ = X.σ 0 x := Edge.id_edge x
        _ = yonedaEquiv (const x) := by
          apply yonedaEquiv.symm.injective
          rw [Equiv.symm_apply_apply, ← stdSimplex.σ_comp_yonedaEquiv_symm,
            yonedaEquiv_symm_zero, comp_const]

private def homotopyROfRelStruct₀ {x : X _⦋0⦌}
    {e e' : Edge x x}
    (h : (edgePtEquiv e).RelStruct₀ (edgePtEquiv e')) :
    Edge.HomotopyR e e' :=
  Edge.CompStruct.mk (yonedaEquiv h.map)
    (d₂ := by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      have h₂ := h.δ_map_of_gt (2 : Fin 3) (by decide)
      rw [h₂, Edge.id_edge]
      apply yonedaEquiv.symm.injective
      rw [Equiv.symm_apply_apply, ← stdSimplex.σ_comp_yonedaEquiv_symm,
        yonedaEquiv_symm_zero, comp_const])
    (d₀ := by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      have h₀ := congrArg yonedaEquiv h.δ_castSucc_map
      simpa [edgePtEquiv] using h₀)
    (d₁ := by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      have h₁ := congrArg yonedaEquiv h.δ_succ_map
      simpa [edgePtEquiv] using h₁)

private noncomputable def πOneToHom {x : X _⦋0⦌} :
    KanComplex.π 1 X x → (mk x ⟶ mk x) :=
  Quot.lift (fun p ↦ homMk (edgePtEquiv.symm p)) (by
    rintro p q ⟨h⟩
    rw [homMk_eq_iff_nonempty_homotopyR]
    exact ⟨homotopyROfRelStruct₀ ((PtSimplex.Homotopy.relStruct₀ h).copy
      (edgePtEquiv.apply_symm_apply p).symm
      (edgePtEquiv.apply_symm_apply q).symm)⟩)

@[simp]
private lemma πOneToHom_mk {x : X _⦋0⦌} (p : X.PtSimplex 1 x) :
    πOneToHom (KanComplex.π.mk p) = homMk (edgePtEquiv.symm p) :=
  rfl

private noncomputable def homEquiv {x : X _⦋0⦌} :
    (mk x ⟶ mk x) ≃ KanComplex.π 1 X x :=
  (Equiv.ofBijective πOneToHom (by
    constructor
    · intro a b hab
      obtain ⟨p, rfl⟩ := a.mk_surjective
      obtain ⟨q, rfl⟩ := b.mk_surjective
      rw [KanComplex.π.mk_eq_mk_iff]
      change homMk (edgePtEquiv.symm p) = homMk (edgePtEquiv.symm q) at hab
      rw [homMk_eq_iff_nonempty_homotopyR] at hab
      obtain ⟨h⟩ := hab
      exact ⟨(relStruct₀OfHomotopyR h).copy
        (edgePtEquiv.apply_symm_apply p) (edgePtEquiv.apply_symm_apply q)⟩
    · intro φ
      obtain ⟨e, rfl⟩ := homMk_surjective φ
      exact ⟨KanComplex.π.mk (edgePtEquiv e), by
        change homMk (edgePtEquiv.symm (edgePtEquiv e)) = homMk e
        rw [edgePtEquiv.symm_apply_apply]⟩)).symm

@[simp]
private lemma homEquiv_homMk {x : X _⦋0⦌} (e : Edge x x) :
    homEquiv (homMk e) = KanComplex.π.mk (edgePtEquiv e) := by
  apply homEquiv.symm.injective
  simp only [homEquiv, Equiv.symm_symm, Equiv.apply_symm_apply]
  change homMk e = homMk (edgePtEquiv.symm (edgePtEquiv e))
  rw [edgePtEquiv.symm_apply_apply]

private lemma homEquiv_map_homMk {x : X _⦋0⦌} (e : Edge x x)
    (f : X ⟶ Y) [KanComplex Y] :
    homEquiv (homMk (e.map f)) =
      KanComplex.π.map f rfl 1 (homEquiv (homMk e)) := by
  rw [homEquiv_homMk, homEquiv_homMk, KanComplex.π.map_mk]
  congr 1
  apply RelativeMorphism.ext
  change yonedaEquiv.symm (f.app _ e.edge) = yonedaEquiv.symm e.edge ≫ f
  exact (yonedaEquiv_symm_comp e.edge f).symm

set_option backward.isDefEq.respectTransparency.types false in
private lemma homEquiv_map {x : X _⦋0⦌} (φ : mk x ⟶ mk x)
    (f : X ⟶ Y) [KanComplex Y] :
    homEquiv ((mapFundamentalGroupoid f).map φ) =
      KanComplex.π.map f rfl 1 (homEquiv φ) := by
  obtain ⟨e, rfl⟩ := homMk_surjective φ
  rw [mapFundamentalGroupoid_map_homMk]
  exact homEquiv_map_homMk e f

private def compStructOfMulStruct {x : X _⦋0⦌}
    {p q r : X.PtSimplex 1 x}
    (h : PtSimplex.MulStruct p q r (0 : Fin 1)) :
    Edge.CompStruct (edgePtEquiv.symm p) (edgePtEquiv.symm q)
      (edgePtEquiv.symm r) :=
  Edge.CompStruct.mk (yonedaEquiv h.map)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      simpa [edgePtEquiv] using congrArg yonedaEquiv h.δ_succ_succ_map)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      simpa [edgePtEquiv] using congrArg yonedaEquiv h.δ_castSucc_castSucc_map)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      simpa [edgePtEquiv] using congrArg yonedaEquiv h.δ_succ_castSucc_map)

private def actionHomotopy {x y : X _⦋0⦌} {s : X.PtSimplex 1 x}
    {t : X.PtSimplex 1 y} {e : X.Edge x y}
    (A : SSet.KanComplex.FundamentalGroupoid.ActionStruct e s t) :
    SSet.Homotopy (RelativeMorphism.map s) (RelativeMorphism.map t) where
  h := A.prism
  h₀ := A.left
  h₁ := A.right
  rel := by
    ext n ⟨⟨z, hz⟩, w⟩
    cases hz

end PiOneComparison

end KanComplex

end SSet

public section

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

namespace KanComplex

open _root_.SSet.FundamentalGroupoid

section PiOneComparison

variable [KanComplex X]

/-- The first simplicial homotopy group of a Kan complex is multiplicatively
equivalent to the endomorphism group at the corresponding object of its
fundamental groupoid. The inverse on the endomorphism is forced by the
opposite multiplication convention on `CategoryTheory.End`. -/
noncomputable def piOneMulEquivFundamentalGroupoidEnd
    (x : X _⦋0⦌) :
    KanComplex.π 1 X x ≃* End (mk x) where
  toFun a := .of (CategoryTheory.inv (πOneToHom a))
  invFun f := homEquiv (CategoryTheory.inv f.asHom)
  left_inv a := by
    change homEquiv (CategoryTheory.inv (CategoryTheory.inv (πOneToHom a))) = a
    rw [IsIso.inv_inv]
    change homEquiv (homEquiv.symm a) = a
    exact homEquiv.apply_symm_apply a
  right_inv f := by
    apply End.ext
    change CategoryTheory.inv (πOneToHom (homEquiv (CategoryTheory.inv f.asHom))) = f.asHom
    rw [show πOneToHom (homEquiv (CategoryTheory.inv f.asHom)) = CategoryTheory.inv f.asHom by
      change homEquiv.symm (homEquiv (CategoryTheory.inv f.asHom)) = CategoryTheory.inv f.asHom
      exact homEquiv.symm_apply_apply _]
    exact IsIso.inv_inv
  map_mul' a b := by
    apply End.ext
    induction a using KanComplex.π.rec with
    | mk p =>
      induction b using KanComplex.π.rec with
      | mk q =>
        obtain ⟨r, ⟨h⟩⟩ := PtSimplex.MulStruct.nonempty p q (0 : Fin 1)
        rw [h.mul_eq]
        rw [End.mul_asHom]
        change CategoryTheory.inv (homMk (edgePtEquiv.symm r)) =
          CategoryTheory.inv (homMk (edgePtEquiv.symm q)) ≫
            CategoryTheory.inv (homMk (edgePtEquiv.symm p))
        rw [← (compStructOfMulStruct h).homMk_comp]
        exact IsIso.inv_comp

/-- On a pointed one-simplex, the multiplicative comparison is the inverse of
the corresponding edge in the fundamental groupoid. -/
@[simp]
theorem piOneMulEquivFundamentalGroupoidEnd_mk
    (x : X _⦋0⦌) (p : X.PtSimplex 1 x) :
    KanComplex.piOneMulEquivFundamentalGroupoidEnd x (KanComplex.π.mk p) =
      End.of (CategoryTheory.inv (homMk
        (Edge.mk (yonedaEquiv (RelativeMorphism.map p))
          (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
          (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const]) :
          Edge x x))) := by
  rfl

/-- The multiplicative first-homotopy-group comparison is natural under maps
of Kan complexes. -/
theorem piOneMulEquivFundamentalGroupoidEnd_naturality
    (f : X ⟶ Y) [KanComplex Y] (x : X _⦋0⦌) (a : KanComplex.π 1 X x) :
    KanComplex.piOneMulEquivFundamentalGroupoidEnd (X := Y) (f.app _ x)
        (KanComplex.π.map f rfl 1 a) =
      (mapFundamentalGroupoid f).mapEnd (mk x)
        (KanComplex.piOneMulEquivFundamentalGroupoidEnd (X := X) x a) := by
  apply End.ext
  induction a using KanComplex.π.rec with
  | mk p =>
    rw [KanComplex.π.map_mk,
      piOneMulEquivFundamentalGroupoidEnd_mk,
      piOneMulEquivFundamentalGroupoidEnd_mk]
    let ep : X.Edge x x :=
      Edge.mk (yonedaEquiv (RelativeMorphism.map p))
        (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
        (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
    let efp : Y.Edge (f.app _ x) (f.app _ x) :=
      Edge.mk (yonedaEquiv (RelativeMorphism.map (PtSimplex.map f rfl p)))
        (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
        (by simp [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
    have hedge : efp = ep.map f := by
      apply Edge.ext
      exact yonedaEquiv_comp _ _
    change CategoryTheory.inv (homMk efp) =
      (mapFundamentalGroupoid f).map (CategoryTheory.inv (homMk ep))
    rw [hedge]
    set_option backward.isDefEq.respectTransparency.types false in
      calc
        CategoryTheory.inv (homMk (ep.map f)) =
            CategoryTheory.inv ((mapFundamentalGroupoid f).map (homMk ep)) := by
          exact congrArg
            (fun z : (mapFundamentalGroupoid f).obj (mk x) ⟶
                (mapFundamentalGroupoid f).obj (mk x) ↦ CategoryTheory.inv z)
            (mapFundamentalGroupoid_map_homMk f ep).symm
        _ = (mapFundamentalGroupoid f).map (CategoryTheory.inv (homMk ep)) :=
          ((mapFundamentalGroupoid f).map_inv (homMk ep)).symm

/-- Under the first-homotopy-group comparison, fundamental-groupoid transport
is conjugation by the transporting morphism. -/
theorem piOneMulEquivFundamentalGroupoidEnd_action {x y : X _⦋0⦌}
    (q : mk x ⟶ mk y) (a : KanComplex.π 1 X x) :
    piOneMulEquivFundamentalGroupoidEnd y (KanComplex.π.action q a) =
      (asIso q).conj (piOneMulEquivFundamentalGroupoidEnd x a) := by
  apply End.ext
  induction q using _root_.SSet.FundamentalGroupoid.hom_rec_of_kanComplex with
  | homMk e =>
    induction a using KanComplex.π.rec with
    | mk s =>
      obtain ⟨t, ⟨A⟩⟩ :=
        SSet.KanComplex.FundamentalGroupoid.exists_actionStruct e s
      rw [KanComplex.π.action_homMk_mk_eq_mk_of_actionStruct A,
        piOneMulEquivFundamentalGroupoidEnd_mk,
        piOneMulEquivFundamentalGroupoidEnd_mk, Iso.conj_apply_asHom]
      change CategoryTheory.inv (homMk (edgePtEquiv.symm t)) =
        CategoryTheory.inv (homMk e) ≫
          CategoryTheory.inv (homMk (edgePtEquiv.symm s)) ≫ homMk e
      let v₀ : (Δ[1] : SSet.{u}) _⦋0⦌ :=
        stdSimplex.obj₀Equiv.symm (0 : Fin 2)
      let v₁ : (Δ[1] : SSet.{u}) _⦋0⦌ :=
        stdSimplex.obj₀Equiv.symm (1 : Fin 2)
      let d : (Δ[1] : SSet.{u}).Edge v₀ v₁ :=
        Edge.mk (stdSimplex.edge.{u} 1 (0 : Fin 2) (1 : Fin 2) (by decide))
          (by
            dsimp [v₀]
            apply stdSimplex.obj₀Equiv.injective
            decide)
          (by
            dsimp [v₁]
            apply stdSimplex.obj₀Equiv.injective
            decide)
      have hv₀ : v₀ = yonedaEquiv (stdSimplex.δ (1 : Fin 2)) := by
        dsimp [v₀]
        rw [stdSimplex.δ_one_eq_const, yonedaEquiv_const]
      have hv₁ : v₁ = yonedaEquiv (stdSimplex.δ (0 : Fin 2)) := by
        dsimp [v₁]
        rw [stdSimplex.δ_zero_eq_const, yonedaEquiv_const]
      have hs₀ : (RelativeMorphism.map s).app _ v₀ = x := by
        rw [hv₀, ← yonedaEquiv_comp, PtSimplex.δ_map, yonedaEquiv_const]
      have hs₁ : (RelativeMorphism.map s).app _ v₁ = x := by
        rw [hv₁, ← yonedaEquiv_comp, PtSimplex.δ_map, yonedaEquiv_const]
      have ht₀ : (RelativeMorphism.map t).app _ v₀ = y := by
        rw [hv₀, ← yonedaEquiv_comp, PtSimplex.δ_map, yonedaEquiv_const]
      have ht₁ : (RelativeMorphism.map t).app _ v₁ = y := by
        rw [hv₁, ← yonedaEquiv_comp, PtSimplex.δ_map, yonedaEquiv_const]
      let es : X.Edge x x := (d.map (RelativeMorphism.map s)).ofEq hs₀ hs₁
      let et : X.Edge y y := (d.map (RelativeMorphism.map t)).ofEq ht₀ ht₁
      have hes : es = edgePtEquiv.symm s := by
        apply Edge.ext
        change (RelativeMorphism.map s).app _
          (stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide)) =
            yonedaEquiv (RelativeMorphism.map s)
        rw [show stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide) =
          yonedaEquiv (𝟙 (Δ[1] : SSet)) by decide]
        simpa using yonedaEquiv_symm_app_id (yonedaEquiv (RelativeMorphism.map s))
      have het : et = edgePtEquiv.symm t := by
        apply Edge.ext
        change (RelativeMorphism.map t).app _
          (stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide)) =
            yonedaEquiv (RelativeMorphism.map t)
        rw [show stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide) =
          yonedaEquiv (𝟙 (Δ[1] : SSet)) by decide]
        simpa using yonedaEquiv_symm_app_id (yonedaEquiv (RelativeMorphism.map t))
      let H := actionHomotopy A
      let h := H.toSimplicialObjectHomotopy
      have hcomponent (i : Fin 2) :
          (Edge.ofSimplicialObjectHomotopy h
            (stdSimplex.obj₀Equiv.symm i)).edge = e.edge := by
        rw [Edge.ofSimplicialObjectHomotopy_edge]
        fin_cases i
        · change ((yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm 0) ▷
              (Δ[1] : SSet)) ≫ A.prism).app _
            (prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1 = e.edge
          have hv : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
              yonedaEquiv (stdSimplex.δ (1 : Fin 2)) := by
            rw [stdSimplex.δ_one_eq_const, yonedaEquiv_const]
          have hb : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet)) ≫ A.prism =
              snd (Δ[0] : SSet) (Δ[1] : SSet) ≫ yonedaEquiv.symm e.edge := by
            rw [← boundary.ι_ι (i := (1 : Fin 2)),
              MonoidalCategory.comp_whiskerRight, Category.assoc, A.boundary,
              ← Category.assoc, CartesianMonoidalCategory.whiskerRight_snd]
          rw [hv, Equiv.symm_apply_apply, hb]
          change (snd (Δ[0] : SSet) (Δ[1] : SSet) ≫
            yonedaEquiv.symm e.edge).app _
              (prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1 = e.edge
          change (snd (Δ[0] : SSet) (Δ[1] : SSet) ≫
            yonedaEquiv.symm e.edge).app _
              (yonedaEquiv (prodStdSimplex₁.ι (0 : Fin 1))) = e.edge
          rw [← yonedaEquiv_comp, ← Category.assoc, prodStdSimplex₁.ι_snd]
          rw [show stdSimplex.objMk₁ ((0 : Fin 1).castSucc.succ) =
            yonedaEquiv (𝟙 (Δ[1] : SSet)) by
              apply stdSimplex.objEquiv.injective
              decide, Equiv.symm_apply_apply, Category.id_comp,
            Equiv.apply_symm_apply]
        · change ((yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm 1) ▷
              (Δ[1] : SSet)) ≫ A.prism).app _
            (prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1 = e.edge
          have hv : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
              yonedaEquiv (stdSimplex.δ (0 : Fin 2)) := by
            rw [stdSimplex.δ_zero_eq_const, yonedaEquiv_const]
          have hb : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet)) ≫ A.prism =
              snd (Δ[0] : SSet) (Δ[1] : SSet) ≫ yonedaEquiv.symm e.edge := by
            rw [← boundary.ι_ι (i := (0 : Fin 2)),
              MonoidalCategory.comp_whiskerRight, Category.assoc, A.boundary,
              ← Category.assoc, CartesianMonoidalCategory.whiskerRight_snd]
          rw [hv, Equiv.symm_apply_apply, hb]
          change (snd (Δ[0] : SSet) (Δ[1] : SSet) ≫
            yonedaEquiv.symm e.edge).app _
              (prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1 = e.edge
          change (snd (Δ[0] : SSet) (Δ[1] : SSet) ≫
            yonedaEquiv.symm e.edge).app _
              (yonedaEquiv (prodStdSimplex₁.ι (0 : Fin 1))) = e.edge
          rw [← yonedaEquiv_comp, ← Category.assoc, prodStdSimplex₁.ι_snd]
          rw [show stdSimplex.objMk₁ ((0 : Fin 1).castSucc.succ) =
            yonedaEquiv (𝟙 (Δ[1] : SSet)) by
              apply stdSimplex.objEquiv.injective
              decide, Equiv.symm_apply_apply, Category.id_comp,
            Equiv.apply_symm_apply]
      let e₀ : X.Edge x y :=
        (Edge.ofSimplicialObjectHomotopy h v₀).ofEq hs₀ ht₀
      let e₁ : X.Edge x y :=
        (Edge.ofSimplicialObjectHomotopy h v₁).ofEq hs₁ ht₁
      have he₀ : e₀ = e := by
        apply Edge.ext
        exact hcomponent 0
      have he₁ : e₁ = e := by
        apply Edge.ext
        exact hcomponent 1
      let η := congrMapFundamentalGroupoid' h
      have hnat := η.hom.naturality (homMk d)
      have hη₀ : η.hom.app (mk v₀) =
          homMk (Edge.ofSimplicialObjectHomotopy h v₀) := rfl
      have hη₁ : η.hom.app (mk v₁) =
          homMk (Edge.ofSimplicialObjectHomotopy h v₁) := rfl
      have hnat' :
          homMk (d.map (RelativeMorphism.map s)) ≫
              homMk (Edge.ofSimplicialObjectHomotopy h v₁) =
            homMk (Edge.ofSimplicialObjectHomotopy h v₀) ≫
              homMk (d.map (RelativeMorphism.map t)) := by
        set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
            rw [hη₀, hη₁] at hnat
            simpa only [mapFundamentalGroupoid_map_homMk] using hnat
      have homMk_edge_ofEq : ∀ {x₀ x₁ y₀ y₁ : X _⦋0⦌}
          (e' : X.Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁),
          homMk (e'.ofEq h₀ h₁) =
            eqToHom (congrArg _root_.SSet.FundamentalGroupoid.mk h₀).symm ≫
              homMk e' ≫ eqToHom (congrArg _root_.SSet.FundamentalGroupoid.mk h₁) := by
        intro x₀ x₁ y₀ y₁ e' h₀ h₁
        cases h₀
        cases h₁
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        congr 1
      have hsquare : homMk es ≫ homMk e₁ = homMk e₀ ≫ homMk et := by
        dsimp only [es, et, e₀, e₁]
        simpa only [homMk_edge_ofEq, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp] using congrArg
            (fun z ↦ eqToHom
                (congrArg _root_.SSet.FundamentalGroupoid.mk hs₀).symm ≫ z ≫
              eqToHom (congrArg _root_.SSet.FundamentalGroupoid.mk ht₁)) hnat'
      rw [hes, het, he₀, he₁] at hsquare
      have hdirect : homMk (edgePtEquiv.symm t) =
          CategoryTheory.inv (homMk e) ≫
            homMk (edgePtEquiv.symm s) ≫ homMk e := by
        rw [← cancel_epi (homMk e)]
        simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hsquare.symm
      rw [hdirect]
      simp only [IsIso.inv_comp, IsIso.inv_inv, Category.assoc]

private lemma bijective_π_map_one_iff (f : X ⟶ Y) [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    Function.Bijective (KanComplex.π.map f h 1) ↔
      Function.Bijective
        ((mapFundamentalGroupoid f).map (X := mk x) (Y := mk x)) := by
  subst y
  rw [← Function.Bijective.of_comp_iff _ (homEquiv (X := X) (x := x)).bijective]
  have hfun :
      KanComplex.π.map (x := x) f rfl 1 ∘ homEquiv =
        homEquiv ∘ (mapFundamentalGroupoid f).map := by
    funext φ
    exact (homEquiv_map φ f).symm
  rw [hfun]
  exact Function.Bijective.of_comp_iff'
    (homEquiv (X := Y) (x := f.app _ x)).bijective _

end PiOneComparison

section Characterization

variable [KanComplex X] [KanComplex Y]

set_option backward.isDefEq.respectTransparency.types false in
/-- A map of Kan complexes induces an equivalence of fundamental groupoids
exactly when it is bijective on connected components and on every fundamental
group at a source basepoint. -/
theorem isEquivalence_mapFundamentalGroupoid_iff (f : X ⟶ Y) :
    (mapFundamentalGroupoid f).IsEquivalence ↔
      Function.Bijective (mapπ₀ f) ∧
        ∀ (x : X _⦋0⦌), Function.Bijective (π.map (x := x) f rfl 1) := by
  constructor
  · intro
    constructor
    · constructor
      · rw [FundamentalGroupoid.mapπ₀_injective_iff]
        rintro x x' ⟨e⟩
        exact ⟨(mapFundamentalGroupoid f).preimageIso e⟩
      · rw [FundamentalGroupoid.mapπ₀_surjective_iff]
        infer_instance
    · intro x
      rw [bijective_π_map_one_iff f rfl]
      apply Functor.FullyFaithful.map_bijective
      apply Functor.FullyFaithful.ofFullyFaithful
  · rintro ⟨h₀, h₁⟩
    simp_rw [bijective_π_map_one_iff f rfl] at h₁
    let _ : (mapFundamentalGroupoid f).EssSurj := by
      rw [← FundamentalGroupoid.mapπ₀_surjective_iff]
      exact h₀.2
    let _ : (mapFundamentalGroupoid f).Faithful := ⟨by
      intro x₀ x₁ g g' h
      have e : x₁ ≅ x₀ := (asIso g').symm
      rw [← cancel_mono e.hom]
      apply (h₁ x₀.pt).1
      simpa only [Functor.map_comp] using
        congrArg (fun k ↦ k ≫ (mapFundamentalGroupoid f).map e.hom) h⟩
    let _ : (mapFundamentalGroupoid f).Full := ⟨fun {x₀ x₁} φ ↦ by
      have e : x₁ ≅ x₀ :=
        ((FundamentalGroupoid.mapπ₀_injective_iff f).1 h₀.1 _ _
          ⟨(asIso φ).symm⟩).some
      obtain ⟨g, hg⟩ := (h₁ x₀.pt).2
        (φ ≫ (mapFundamentalGroupoid f).map e.hom)
      exact ⟨g ≫ e.inv, by aesop⟩⟩
    exact {}

/-- For a map between Kan complexes, `KanComplex.W` is equivalent to
bijectivity on connected components and every positive homotopy group. -/
theorem W_iff (f : X ⟶ Y) :
    W f ↔ Function.Bijective (mapπ₀ f) ∧
      ∀ (n : ℕ) (x : X _⦋0⦌),
        Function.Bijective (π.map (x := x) f rfl (n + 1)) := by
  constructor
  · intro hf
    exact ⟨((isEquivalence_mapFundamentalGroupoid_iff f).mp
      hf.isEquivalence_mapFundamentalGroupoid).1,
      fun n x ↦ hf.bijective_piMap (n + 1) x⟩
  · rintro ⟨h₀, hπ⟩
    apply W.mk f inferInstance inferInstance
    · rw [isEquivalence_mapFundamentalGroupoid_iff]
      exact ⟨h₀, fun x ↦ hπ 0 x⟩
    · rintro (_ | n) x
      · exact (bijective_mapπ₀_iff_bijective_mapπ_zero f x _ rfl).mpr h₀
      · exact hπ n x

end Characterization

/-- A `KanComplex.W` map is bijective on connected components. -/
theorem W.bijective_mapπ₀ {f : X ⟶ Y} (hf : W f) :
    Function.Bijective (mapπ₀ f) := by
  let _ : KanComplex X := hf.kanComplex_source
  let _ : KanComplex Y := hf.kanComplex_target
  exact ((W_iff f).mp hf).1

end KanComplex

end SSet
