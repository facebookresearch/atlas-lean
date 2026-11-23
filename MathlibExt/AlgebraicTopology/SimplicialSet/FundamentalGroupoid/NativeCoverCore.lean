/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveEquiv
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomotopyPullback
public import MathlibExt.CategoryTheory.Functor.Isofibration
import Mathlib.Tactic.FinCases

/-!
# Native covers and pointed simplex lifts
-/

set_option autoImplicit false

/-!
## Native path projection and pointed higher-simplex lifts

The original fundamental-groupoid nerve unit is pulled back along the nerve
of the original under-category projection.  Relative nerve horn lifts give
the Kan property, and the identity path supplies the chosen pullback point.
Pointed simplices in dimension at least two lift through these original maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace CategoryTheory.Under

section Category

variable {C : Type u} [Category.{v} C] (y : C)

/-- The original projection lifts every isomorphism to its literal postcomposed object. -/
instance forget_isIsofibration : (Under.forget y).IsIsofibration := by
  apply Functor.isIsofibration_of_exists_lift_hom
  intro U z g hg
  let V : Under y := Under.mk (U.hom ≫ g)
  let f : U ⟶ V := Under.homMk g rfl
  let : IsIso ((Under.forget y).map f) := by
    change IsIso g
    exact hg
  refine ⟨V, f, rfl, isIso_of_reflects_iso f (Under.forget y), ?_⟩
  change g ≫ eqToHom (rfl : z = z) = g
  simp only [eqToHom_refl, Category.comp_id]

end Category

section Groupoid

variable {C : Type u} [Groupoid.{v} C] (y : C)

/-- Standard reflected inversion makes the original under category a groupoid. -/
instance isGroupoid : IsGroupoid (Under y) :=
  isGroupoid_of_reflects_iso (Under.forget y)

end Groupoid

end CategoryTheory.Under

namespace CategoryTheory.nerve

variable {C D : Type u} [Category.{v} C] [Groupoid.{v} D]

/-- Lift an original nerve edge with its first endpoint prescribed on the nose. -/
theorem exists_oneSimplexLift_from (F : C ⥤ D) [F.IsIsofibration]
    (x : C) (s : ComposableArrows D 1) (hx : F.obj x = s.left) :
    ∃ t : ComposableArrows C 1,
      t.left = x ∧ (nerveMap F).app (op ⦋1⦌) t = s := by
  let g : F.obj x ≅ s.right := eqToIso hx ≪≫ asIso s.hom
  obtain ⟨y, e, hy, he⟩ := F.exists_iso_lift g
  refine ⟨ComposableArrows.mk₁ e.hom, rfl, ?_⟩
  rw [nerveMap_app_mk₁]
  apply ComposableArrows.ext₁ hx hy
  have h : F.map e.hom ≫ eqToHom hy = eqToHom hx ≫ s.hom := by
    simpa [g] using congrArg Iso.hom he
  have hproj : (ComposableArrows.mk₁ (F.map e.hom)).hom = F.map e.hom := rfl
  apply (cancel_mono (eqToHom hy)).mp
  simpa only [hproj, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h

/-- Lift an original nerve edge with its last endpoint prescribed on the nose. -/
theorem exists_oneSimplexLift_to (F : C ⥤ D) [F.IsIsofibration]
    (x : C) (s : ComposableArrows D 1) (hx : F.obj x = s.right) :
    ∃ t : ComposableArrows C 1,
      t.right = x ∧ (nerveMap F).app (op ⦋1⦌) t = s := by
  let g : F.obj x ≅ s.left := eqToIso hx ≪≫ (asIso s.hom).symm
  obtain ⟨y, e, hy, he⟩ := F.exists_iso_lift g
  refine ⟨ComposableArrows.mk₁ e.inv, rfl, ?_⟩
  rw [nerveMap_app_mk₁]
  apply ComposableArrows.ext₁ hy hx
  have h : eqToHom hy.symm ≫ F.map e.inv = s.hom ≫ eqToHom hx.symm := by
    simpa [g] using congrArg Iso.inv he
  have hproj : (ComposableArrows.mk₁ (F.map e.inv)).hom = F.map e.inv := rfl
  apply (cancel_epi (eqToHom hy.symm)).mp
  simpa only [hproj, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] using h


/-- An ordinary isofibration to a groupoid lifts the original one-horn square,
with the original base simplex and nerve projection preserved exactly. -/
theorem exists_oneHornProjectionLift (F : C ⥤ D) [F.IsIsofibration]
    (i : Fin 2)
    (f : ∀ (j : Fin 2) (_ : j ≠ i),
      (Δ[0] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (β : (Δ[1] : SSet.{max u v}) ⟶ CategoryTheory.nerve D)
    (hf : ∀ (j : Fin 2) (hj : j ≠ i),
      f j hj ≫ nerveMap F = SSet.stdSimplex.δ j ≫ β) :
    ∃ φ : (Δ[1] : SSet.{max u v}) ⟶ CategoryTheory.nerve C,
      (∀ (j : Fin 2) (hj : j ≠ i), SSet.stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ nerveMap F = β := by
  fin_cases i
  · let h10 : (1 : Fin 2) ≠ 0 := by decide
    let z : ComposableArrows C 0 := SSet.yonedaEquiv (f 1 h10)
    let s : ComposableArrows D 1 := SSet.yonedaEquiv β
    have hx : F.obj z.left = s.left := by
      have h := congrArg
        (fun q : (Δ[0] : SSet.{max u v}) ⟶ CategoryTheory.nerve D =>
          (SSet.yonedaEquiv q).left) (hf 1 h10)
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp] at h
      change F.obj z.left = s.left at h
      exact h
    obtain ⟨t, ht, hp⟩ := exists_oneSimplexLift_from F z.left s hx
    have hyt : SSet.yonedaEquiv
        (SSet.yonedaEquiv.symm t : (Δ[1] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) = t :=
      (SSet.yonedaEquiv (X := CategoryTheory.nerve C) (n := ⦋1⦌)).apply_symm_apply t
    refine ⟨SSet.yonedaEquiv.symm t, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · contradiction
      · have hh : hj = h10 := Subsingleton.elim _ _
        subst hh
        apply SSet.yonedaEquiv.injective
        rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
        rw [hyt]
        apply ComposableArrows.ext₀
        exact ht
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      rw [hyt]
      simpa only [s] using hp
  · let h01 : (0 : Fin 2) ≠ 1 := by decide
    let z : ComposableArrows C 0 := SSet.yonedaEquiv (f 0 h01)
    let s : ComposableArrows D 1 := SSet.yonedaEquiv β
    have hx : F.obj z.left = s.right := by
      have h := congrArg
        (fun q : (Δ[0] : SSet.{max u v}) ⟶ CategoryTheory.nerve D =>
          (SSet.yonedaEquiv q).left) (hf 0 h01)
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp] at h
      change F.obj z.left = s.right at h
      exact h
    obtain ⟨t, ht, hp⟩ := exists_oneSimplexLift_to F z.left s hx
    have hyt : SSet.yonedaEquiv
        (SSet.yonedaEquiv.symm t : (Δ[1] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) = t :=
      (SSet.yonedaEquiv (X := CategoryTheory.nerve C) (n := ⦋1⦌)).apply_symm_apply t
    refine ⟨SSet.yonedaEquiv.symm t, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · have hh : hj = h01 := Subsingleton.elim _ _
        subst hh
        apply SSet.yonedaEquiv.injective
        rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
        rw [hyt]
        apply ComposableArrows.ext₀
        exact ht
      · contradiction
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      rw [hyt]
      simpa only [s] using hp

end CategoryTheory.nerve

namespace CategoryTheory.nerve

variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]

/-- An actual isofibration between homogeneous groupoids lifts every original
compatible nerve horn over its original base simplex and projection. -/
theorem exists_hornProjectionLift (F : C ⥤ D) [F.IsIsofibration]
    {n : ℕ} {i : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      (Δ[n] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (hf : SSet.horn.IsCompatible f)
    (β : (Δ[n + 1] : SSet.{max u v}) ⟶ CategoryTheory.nerve D)
    (comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      f j hj ≫ nerveMap F = SSet.stdSimplex.δ j ≫ β) :
    ∃ φ : (Δ[n + 1] : SSet.{max u v}) ⟶ CategoryTheory.nerve C,
      (∀ (j : Fin (n + 2)) (hj : j ≠ i), SSet.stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ nerveMap F = β := by
  cases n with
  | zero => exact exists_oneHornProjectionLift F i f β comm
  | succ m =>
    let : SSet.KanComplex (CategoryTheory.nerve C) :=
      SSet.kanComplex_nerve_of_groupoid C
    obtain ⟨φ, hφ⟩ := hf.exists_lift_of_kanComplex
    refine ⟨φ, hφ, ?_⟩
    have hrestrict : (SSet.horn (m + 2) i).ι ≫ (φ ≫ nerveMap F) =
        (SSet.horn (m + 2) i).ι ≫ β := by
      apply SSet.horn.hom_ext'
      intro j hj
      simp only [← Category.assoc, SSet.horn.ι_ι]
      rw [hφ j hj]
      exact comm j hj
    have hs : SSet.yonedaEquiv.symm (SSet.yonedaEquiv (φ ≫ nerveMap F)) =
        φ ≫ nerveMap F :=
      (SSet.yonedaEquiv (X := CategoryTheory.nerve D) (n := ⦋m + 2⦌)).symm_apply_apply _
    have ht : SSet.yonedaEquiv.symm (SSet.yonedaEquiv β) = β :=
      (SSet.yonedaEquiv (X := CategoryTheory.nerve D) (n := ⦋m + 2⦌)).symm_apply_apply β
    apply SSet.yonedaEquiv.injective
    apply CategoryTheory.nerve.eq_of_hornRestriction_eq D i (by omega)
    rw [hs, ht]
    exact hrestrict

/-- The actual native nerve map of a homogeneous groupoid isofibration is
an actual Kan fibration, obtained from the proved original relative horns. -/
theorem fibration_nerveMap_of_isIsofibration (F : C ⥤ D) [F.IsIsofibration] :
    HomotopicalAlgebra.Fibration (nerveMap F) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  refine ⟨fun {α β} sq => ?_⟩
  have comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      (SSet.horn.ι i j hj ≫ α) ≫ nerveMap F = SSet.stdSimplex.δ j ≫ β := by
    intro j hj
    rw [Category.assoc, sq.w, ← Category.assoc, SSet.horn.ι_ι]
  obtain ⟨φ, hφ, hp⟩ := exists_hornProjectionLift F
    (fun j hj => SSet.horn.ι i j hj ≫ α) (SSet.horn.IsCompatible.of_hom α) β comm
  apply CommSq.HasLift.mk'
  refine { l := φ, fac_left := ?_, fac_right := hp }
  apply SSet.horn.hom_ext'
  intro j hj
  simpa only [← Category.assoc, SSet.horn.ι_ι] using hφ j hj

end CategoryTheory.nerve

namespace SSet.KanComplex

/-- Promote the existing category using the accepted original Under groupoid data. -/
@[nolint defsWithUnderscore]
local instance {G : Type u} [Groupoid.{u} G] (y : G) :
    Groupoid.{u} (CategoryTheory.Under y) := Groupoid.ofIsGroupoid

/-- The original fundamental-groupoid nerve unit, evaluated at the identity functor. -/
def nativeCoverUnit (X : SSet.{u}) :
    X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  SSet.fundamentalGroupoidNerveEquiv X (SSet.FundamentalGroupoid X)
    (𝟭 (SSet.FundamentalGroupoid X))

/-- The nerve of the original under-category forgetful projection. -/
def nativeCoverNerveProjection (X : SSet.{u}) (x : X _⦋0⦌) :
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)) ⟶
      CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  CategoryTheory.nerveMap (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x))

/-- The literal pullback of the original unit and original path-groupoid projection. -/
def nativeCover (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  pullback (nativeCoverUnit X) (nativeCoverNerveProjection X x)

/-- The original first pullback projection to the given simplicial set. -/
def nativeCoverProjection (X : SSet.{u}) (x : X _⦋0⦌) : nativeCover X x ⟶ X :=
  pullback.fst (nativeCoverUnit X) (nativeCoverNerveProjection X x)

/-- The original second pullback projection to the under-category nerve. -/
def nativeCoverUnderProjection (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCover X x ⟶
      CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)) :=
  pullback.snd (nativeCoverUnit X) (nativeCoverNerveProjection X x)

/-- The actual original nerve fibration and existing pullback instance make this pullback Kan. -/
theorem nativeCover_kanComplex (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    SSet.KanComplex (nativeCover X x) := by
  let : HomotopicalAlgebra.Fibration (nativeCoverNerveProjection X x) := by
    dsimp only [nativeCoverNerveProjection]
    exact CategoryTheory.nerve.fibration_nerveMap_of_isIsofibration
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x))
  dsimp only [nativeCover]
  infer_instance

private theorem nativeCoverUnit_identity_vertex (X : SSet.{u}) (x : X _⦋0⦌) :
    (nativeCoverUnit X).app (op ⦋0⦌) x =
      (nativeCoverNerveProjection X x).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
  dsimp only [nativeCoverUnit, nativeCoverNerveProjection]
  rw [SSet.fundamentalGroupoidNerveEquiv_app_zero, CategoryTheory.nerveMap_app_mk₀]
  rfl

private theorem nativeCoverIdentitySquare (X : SSet.{u}) (x : X _⦋0⦌) :
    (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm x ≫ nativeCoverUnit X =
      (SSet.yonedaEquiv
        (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
        (n := ⦋0⦌)).symm
          (ComposableArrows.mk₀ (CategoryTheory.Under.mk
            (𝟙 (SSet.FundamentalGroupoid.mk x)))) ≫ nativeCoverNerveProjection X x := by
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let zU : U _⦋0⦌ :=
    ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))
  let aU : (Δ[0] : SSet.{u}) ⟶ U :=
    (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm zU
  have hX :
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm x ≫ nativeCoverUnit X =
        (SSet.yonedaEquiv
          (X := CategoryTheory.nerve (SSet.FundamentalGroupoid X)) (n := ⦋0⦌)).symm
            ((nativeCoverUnit X).app (op ⦋0⦌) x) :=
    SSet.yonedaEquiv_symm_comp
      (X := X) (Y := CategoryTheory.nerve (SSet.FundamentalGroupoid X))
      (n := ⦋0⦌) x (nativeCoverUnit X)
  have hU : aU ≫ nativeCoverNerveProjection X x =
      (SSet.yonedaEquiv
        (X := CategoryTheory.nerve (SSet.FundamentalGroupoid X)) (n := ⦋0⦌)).symm
          ((nativeCoverNerveProjection X x).app (op ⦋0⦌) zU) :=
    SSet.yonedaEquiv_symm_comp
      (X := U) (Y := CategoryTheory.nerve (SSet.FundamentalGroupoid X))
      (n := ⦋0⦌) zU (nativeCoverNerveProjection X x)
  have hv : (nativeCoverUnit X).app (op ⦋0⦌) x =
      (nativeCoverNerveProjection X x).app (op ⦋0⦌) zU :=
    nativeCoverUnit_identity_vertex X x
  have hs :
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm x ≫ nativeCoverUnit X =
        aU ≫ nativeCoverNerveProjection X x :=
    hX.trans ((congrArg
      ((SSet.yonedaEquiv
        (X := CategoryTheory.nerve (SSet.FundamentalGroupoid X)) (n := ⦋0⦌)).symm)
      hv).trans hU.symm)
  exact hs

/-- The actual Δ[0] pullback lift of the given vertex and its original identity path. -/
def nativeCoverIdentityPointMap (X : SSet.{u}) (x : X _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ nativeCover X x :=
  pullback.lift ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm x)
    ((SSet.yonedaEquiv
      (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
      (n := ⦋0⦌)).symm
        (ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))))
    (by exact nativeCoverIdentitySquare X x)

/-- The vertex represented by that literal original Δ[0] pullback lift. -/
def nativeCoverIdentityPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (nativeCover X x) _⦋0⦌ :=
  (SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋0⦌)) (nativeCoverIdentityPointMap X x)

/-- The original cover's identity point projects strictly to the original chosen vertex. -/
@[simp]
theorem nativeCoverProjection_identityPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (nativeCoverProjection X x).app (op ⦋0⦌) (nativeCoverIdentityPoint X x) = x := by
  have h : nativeCoverIdentityPointMap X x ≫ nativeCoverProjection X x =
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm x := by
    dsimp only [nativeCoverIdentityPointMap, nativeCoverProjection]
    exact pullback.lift_fst _ _ _
  have hv := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) h
  rw [SSet.yonedaEquiv_comp] at hv
  dsimp only [nativeCoverIdentityPoint]
  exact hv.trans ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).apply_symm_apply x)

/-- The same point projects strictly to the original identity-path nerve vertex. -/
@[simp]
theorem nativeCoverUnderProjection_identityPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (nativeCoverUnderProjection X x).app (op ⦋0⦌) (nativeCoverIdentityPoint X x) =
      ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x))) := by
  have h : nativeCoverIdentityPointMap X x ≫ nativeCoverUnderProjection X x =
      (SSet.yonedaEquiv
        (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
        (n := ⦋0⦌)).symm
          (ComposableArrows.mk₀ (CategoryTheory.Under.mk
            (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
    dsimp only [nativeCoverIdentityPointMap, nativeCoverUnderProjection]
    exact pullback.lift_snd _ _ _
  have hv := congrArg
    (SSet.yonedaEquiv
      (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
      (n := ⦋0⦌)) h
  rw [SSet.yonedaEquiv_comp] at hv
  dsimp only [nativeCoverIdentityPoint]
  exact hv.trans
    ((SSet.yonedaEquiv
      (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
      (n := ⦋0⦌)).apply_symm_apply
        (ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))))

end SSet.KanComplex


namespace SSet.PtSimplex

/-- The original fundamental-groupoid nerve unit sends every pointed simplex
in degree at least two to the literal constant simplex at the original base object. -/
theorem comp_fundamentalGroupoidNerveUnit_eq_const
    {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    (SSet.RelativeMorphism.map σ) ≫
      SSet.fundamentalGroupoidNerveEquiv X (SSet.FundamentalGroupoid X)
        (𝟭 (SSet.FundamentalGroupoid X)) =
      SSet.const (CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x)) := by
  cases n with
  | zero => exact (Nat.not_succ_le_zero 1 hn).elim
  | succ n =>
    cases n with
    | zero => exact (Nat.not_succ_le_self 1 hn).elim
    | succ k =>
      let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
      let η : X ⟶ Y :=
        SSet.fundamentalGroupoidNerveEquiv X (SSet.FundamentalGroupoid X)
          (𝟭 (SSet.FundamentalGroupoid X))
      let y : Y _⦋0⦌ := η.app (Opposite.op ⦋0⦌) x
      let A : (Δ[k + 2] : SSet.{u}) ⟶ Y := (SSet.RelativeMorphism.map σ) ≫ η
      let B : (Δ[k + 2] : SSet.{u}) ⟶ Y := SSet.const y
      let : (Δ[1] : SSet.{u}).HasDimensionLT (k + 2) :=
        (Δ[1] : SSet.{u}).hasDimensionLT_of_le 2 (k + 2) hn
      have hedge (i : Fin (k + 2)) :
          SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫ A =
            SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫ B := by
        calc
          SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫ A =
              (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫
                (SSet.RelativeMorphism.map σ)) ≫ η :=
            (Category.assoc _ _ _).symm
          _ = (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) ≫ η :=
            congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ X => f ≫ η)
              (SSet.PtSimplex.comp_map_eq_const σ
                (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i)))
          _ = (SSet.const y : (Δ[1] : SSet.{u}) ⟶ Y) :=
            SSet.const_comp x η
          _ = SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫ B :=
            (SSet.comp_const (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i)) y).symm
      have hspine :
          Y.spine (k + 2) (SSet.yonedaEquiv A) =
            Y.spine (k + 2) (SSet.yonedaEquiv B) := by
        apply SSet.Path.ext'
        intro i
        calc
          (Y.spine (k + 2) (SSet.yonedaEquiv A)).arrow i =
              Y.map (SimplexCategory.mkOfSucc i).op (SSet.yonedaEquiv A) :=
            SSet.spine_arrow Y (k + 2) (SSet.yonedaEquiv A) i
          _ = (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌))
              (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫ A) :=
            SSet.yonedaEquiv_naturality (X := Y)
              (m := ⦋1⦌) (n := ⦋k + 2⦌) (SimplexCategory.mkOfSucc i) A
          _ = (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌))
              (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫ B) :=
            congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)) (hedge i)
          _ = Y.map (SimplexCategory.mkOfSucc i).op (SSet.yonedaEquiv B) :=
            (SSet.yonedaEquiv_naturality (X := Y)
              (m := ⦋1⦌) (n := ⦋k + 2⦌) (SimplexCategory.mkOfSucc i) B).symm
          _ = (Y.spine (k + 2) (SSet.yonedaEquiv B)).arrow i :=
            (SSet.spine_arrow Y (k + 2) (SSet.yonedaEquiv B) i).symm
      let sx : Y.StrictSegal :=
        CategoryTheory.Nerve.strictSegal (SSet.FundamentalGroupoid X)
      have hs : SSet.yonedaEquiv A = SSet.yonedaEquiv B :=
        (sx.spineToSimplex_spine_apply (SSet.yonedaEquiv A)).symm.trans
          ((congrArg sx.spineToSimplex hspine).trans
            (sx.spineToSimplex_spine_apply (SSet.yonedaEquiv B)))
      have hAB : A = B :=
        (SSet.yonedaEquiv (X := Y) (n := ⦋k + 2⦌)).injective hs
      have hy : y = CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x) :=
        SSet.fundamentalGroupoidNerveEquiv_app_zero X (SSet.FundamentalGroupoid X)
          (𝟭 (SSet.FundamentalGroupoid X)) x
      exact hAB.trans
        (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[k + 2] : SSet.{u}) ⟶ Y)) hy)

end SSet.PtSimplex


namespace SSet.KanComplex

private theorem nativeCoverPointedLiftSquare
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    (SSet.RelativeMorphism.map σ) ≫ nativeCoverUnit X =
      (SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) :
          (Δ[n] : SSet.{u}) ⟶
            CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))) ≫
        nativeCoverNerveProjection X x := by
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let zU : U _⦋0⦌ :=
    ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))
  let η : X ⟶ Y := nativeCoverUnit X
  let q : U ⟶ Y := nativeCoverNerveProjection X x
  let y : Y _⦋0⦌ := η.app (Opposite.op ⦋0⦌) x
  have hy : y = CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x) :=
    SSet.fundamentalGroupoidNerveEquiv_app_zero X (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) x
  have hσ : (SSet.RelativeMorphism.map σ) ≫ η = (SSet.const y : (Δ[n] : SSet.{u}) ⟶ Y) :=
    (SSet.PtSimplex.comp_fundamentalGroupoidNerveUnit_eq_const σ hn).trans
      (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[n] : SSet.{u}) ⟶ Y)) hy.symm)
  have hv : y = q.app (Opposite.op ⦋0⦌) zU :=
    nativeCoverUnit_identity_vertex X x
  have hq : (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) ≫ q =
      SSet.const (q.app (Opposite.op ⦋0⦌) zU) :=
    SSet.const_comp zU q
  exact hσ.trans ((congrArg
    (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[n] : SSet.{u}) ⟶ Y)) hv).trans hq.symm)

/-- The actual original pullback map of a pointed higher simplex and the identity path. -/
def nativeCoverPointedLiftMap
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    (Δ[n] : SSet.{u}) ⟶ nativeCover X x :=
  pullback.lift (SSet.RelativeMorphism.map σ)
    (SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))))
    (by exact nativeCoverPointedLiftSquare σ hn)

/-- The actual lifted map's original first projection is the given simplex map. -/
theorem nativeCoverPointedLiftMap_projection
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    nativeCoverPointedLiftMap σ hn ≫ nativeCoverProjection X x = (SSet.RelativeMorphism.map σ) := by
  dsimp only [nativeCoverPointedLiftMap, nativeCoverProjection]
  exact pullback.lift_fst _ _ _

/-- Its original second projection is the actual constant identity-path simplex. -/
theorem nativeCoverPointedLiftMap_underProjection
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    nativeCoverPointedLiftMap σ hn ≫ nativeCoverUnderProjection X x =
      SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
  dsimp only [nativeCoverPointedLiftMap, nativeCoverUnderProjection]
  exact pullback.lift_snd _ _ _

private theorem nativeCoverPointedLiftMap_boundary
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    (SSet.boundary n).ι ≫ nativeCoverPointedLiftMap σ hn =
      SSet.const (nativeCoverIdentityPoint X x) := by
  let P : SSet.{u} := nativeCover X x
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
  let zU : U _⦋0⦌ :=
    ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))
  let L : (Δ[n] : SSet.{u}) ⟶ P := nativeCoverPointedLiftMap σ hn
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ U := nativeCoverUnderProjection X x
  have hpL : L ≫ p = (SSet.RelativeMorphism.map σ) := nativeCoverPointedLiftMap_projection σ hn
  have hrL : L ≫ r = (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
    nativeCoverPointedLiftMap_underProjection σ hn
  have hpb : p.app (Opposite.op ⦋0⦌) b = x :=
    nativeCoverProjection_identityPoint X x
  have hrb : r.app (Opposite.op ⦋0⦌) b = zU :=
    nativeCoverUnderProjection_identityPoint X x
  have hp : ((SSet.boundary n).ι ≫ L) ≫ p =
      (SSet.const b : (SSet.boundary n : SSet.{u}) ⟶ P) ≫ p := by
    calc
      ((SSet.boundary n).ι ≫ L) ≫ p = (SSet.boundary n).ι ≫ (L ≫ p) :=
        Category.assoc _ _ _
      _ = (SSet.boundary n).ι ≫ (SSet.RelativeMorphism.map σ) :=
        congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => (SSet.boundary n).ι ≫ f) hpL
      _ = (SSet.const x : (SSet.boundary n : SSet.{u}) ⟶ X) :=
        SSet.PtSimplex.comp_map_eq_const σ (SSet.boundary n).ι
      _ = SSet.const (p.app (Opposite.op ⦋0⦌) b) :=
        congrArg
          (fun z : X _⦋0⦌ => (SSet.const z : (SSet.boundary n : SSet.{u}) ⟶ X)) hpb.symm
      _ = (SSet.const b : (SSet.boundary n : SSet.{u}) ⟶ P) ≫ p :=
        (SSet.const_comp b p).symm
  have hr : ((SSet.boundary n).ι ≫ L) ≫ r =
      (SSet.const b : (SSet.boundary n : SSet.{u}) ⟶ P) ≫ r := by
    calc
      ((SSet.boundary n).ι ≫ L) ≫ r = (SSet.boundary n).ι ≫ (L ≫ r) :=
        Category.assoc _ _ _
      _ = (SSet.boundary n).ι ≫ (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ U => (SSet.boundary n).ι ≫ f) hrL
      _ = (SSet.const zU : (SSet.boundary n : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.boundary n).ι zU
      _ = SSet.const (r.app (Opposite.op ⦋0⦌) b) :=
        congrArg
          (fun z : U _⦋0⦌ => (SSet.const z : (SSet.boundary n : SSet.{u}) ⟶ U)) hrb.symm
      _ = (SSet.const b : (SSet.boundary n : SSet.{u}) ⟶ P) ≫ r :=
        (SSet.const_comp b r).symm
  exact pullback.hom_ext hp hr

/-- The original lifted map satisfies the actual pointed boundary at the identity point. -/
def nativeCoverPointedLift
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x) where
  map := nativeCoverPointedLiftMap σ hn
  comm := by
    have hc :
        (SSet.const
          ⟨nativeCoverIdentityPoint X x,
            SSet.Subcomplex.mem_ofSimplex_obj (nativeCoverIdentityPoint X x)⟩ :
          (SSet.boundary n : SSet.{u}) ⟶
            (SSet.Subcomplex.ofSimplex (nativeCoverIdentityPoint X x) : SSet.{u})) ≫
          (SSet.Subcomplex.ofSimplex (nativeCoverIdentityPoint X x)).ι =
            (SSet.const (nativeCoverIdentityPoint X x) :
              (SSet.boundary n : SSet.{u}) ⟶ nativeCover X x) :=
      SSet.const_comp
        (X := (SSet.boundary n : SSet.{u}))
        (Y := (SSet.Subcomplex.ofSimplex (nativeCoverIdentityPoint X x) : SSet.{u}))
        (Z := nativeCover X x)
        ⟨nativeCoverIdentityPoint X x,
          SSet.Subcomplex.mem_ofSimplex_obj (nativeCoverIdentityPoint X x)⟩
        (SSet.Subcomplex.ofSimplex (nativeCoverIdentityPoint X x)).ι
    exact (nativeCoverPointedLiftMap_boundary σ hn).trans hc.symm

/-- The actual pointed lift retains its original underlying pullback map. -/
@[simp]
theorem nativeCoverPointedLift_map
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    SSet.RelativeMorphism.map (nativeCoverPointedLift σ hn) =
      nativeCoverPointedLiftMap σ hn := rfl

/-- The existing pointed pushforward of the actual lift is the original simplex. -/
theorem nativeCoverProjection_pointedLift
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (σ : X.PtSimplex n x) (hn : 2 ≤ n) :
    SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) (nativeCoverPointedLift σ hn) = σ := by
  apply SSet.RelativeMorphism.ext
  have hm :
      SSet.RelativeMorphism.map
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) (nativeCoverPointedLift σ hn)) =
        SSet.RelativeMorphism.map (nativeCoverPointedLift σ hn) ≫
          nativeCoverProjection X x := rfl
  exact hm.trans ((congrArg
    (fun f : (Δ[n] : SSet.{u}) ⟶ nativeCover X x => f ≫ nativeCoverProjection X x)
    (nativeCoverPointedLift_map σ hn)).trans (nativeCoverPointedLiftMap_projection σ hn))

/-- The original native homotopy map is surjective in every degree at least two. -/
theorem nativeCoverProjection_piMap_surjective
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective
      (SSet.KanComplex.π.map (nativeCoverProjection X x)
        (nativeCoverProjection_identityPoint X x) n) := by
  intro a
  obtain ⟨σ, hσ⟩ := (SSet.KanComplex.π.mk_surjective (X := X) (x := x) (n := n)) a
  refine ⟨SSet.KanComplex.π.mk (nativeCoverPointedLift σ hn), ?_⟩
  exact (SSet.KanComplex.π.map_mk (nativeCoverProjection X x)
    (nativeCoverProjection_identityPoint X x) (nativeCoverPointedLift σ hn)).trans
      ((congrArg (SSet.KanComplex.π.mk (X := X) (x := x) (n := n))
        (nativeCoverProjection_pointedLift σ hn)).trans hσ)

end SSet.KanComplex

namespace SSet.KanComplex

/-- Maps into the original native cover are determined by its two actual projections. -/
theorem nativeCover_hom_ext
    {X : SSet.{u}} {x : X _⦋0⦌} {Z : SSet.{u}}
    {a b : Z ⟶ nativeCover X x}
    (hp : a ≫ nativeCoverProjection X x = b ≫ nativeCoverProjection X x)
    (hr : a ≫ nativeCoverUnderProjection X x = b ≫ nativeCoverUnderProjection X x) :
    a = b := by
  dsimp only [nativeCover, nativeCoverProjection, nativeCoverUnderProjection] at *
  exact pullback.hom_ext hp hr

end SSet.KanComplex
namespace SSet.KanComplex

/-- Every original higher pointed simplex has constant identity-path Under projection. -/
theorem nativeCoverUnderProjection_pointedSimplex_eq_const
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (τ : (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x)) (hn : 2 ≤ n) :
    SSet.RelativeMorphism.map τ ≫ nativeCoverUnderProjection X x =
      SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
  cases n with
  | zero => exact (Nat.not_succ_le_zero 1 hn).elim
  | succ n =>
    cases n with
    | zero => exact (Nat.not_succ_le_self 1 hn).elim
    | succ k =>
      let : Groupoid.{u} (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)) :=
        Groupoid.ofIsGroupoid
      let P : SSet.{u} := nativeCover X x
      let Y : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
      let y : Y _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : P ⟶ Y := nativeCoverUnderProjection X x
      let A : (Δ[k + 2] : SSet.{u}) ⟶ Y := SSet.RelativeMorphism.map τ ≫ r
      let B : (Δ[k + 2] : SSet.{u}) ⟶ Y := SSet.const y
      have hrb : r.app (Opposite.op ⦋0⦌) b = y :=
        nativeCoverUnderProjection_identityPoint X x
      have hface (j : Fin (k + 3)) : SSet.stdSimplex.δ j ≫ A = SSet.stdSimplex.δ j ≫ B := by
        have hτ : SSet.stdSimplex.δ j ≫ SSet.RelativeMorphism.map τ =
            (SSet.const b : (Δ[k + 1] : SSet.{u}) ⟶ P) :=
          SSet.PtSimplex.δ_map τ j
        have ha : SSet.stdSimplex.δ j ≫ A =
            (SSet.const y : (Δ[k + 1] : SSet.{u}) ⟶ Y) :=
          (Category.assoc _ _ _).symm.trans
            ((congrArg (fun f : (Δ[k + 1] : SSet.{u}) ⟶ P => f ≫ r) hτ).trans
              ((SSet.const_comp b r).trans
                (congrArg
                  (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[k + 1] : SSet.{u}) ⟶ Y)) hrb)))
        exact ha.trans (SSet.comp_const (SSet.stdSimplex.δ j) y).symm
      have hhorn : (SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫ A =
          (SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫ B := by
        apply SSet.horn.hom_ext'
        intro j hj
        simpa only [← Category.assoc, SSet.horn.ι_ι] using hface j
      have hA :
          (SSet.yonedaEquiv (X := Y) (n := ⦋k + 2⦌)).symm (SSet.yonedaEquiv A) = A :=
        (SSet.yonedaEquiv (X := Y) (n := ⦋k + 2⦌)).symm_apply_apply A
      have hB :
          (SSet.yonedaEquiv (X := Y) (n := ⦋k + 2⦌)).symm (SSet.yonedaEquiv B) = B :=
        (SSet.yonedaEquiv (X := Y) (n := ⦋k + 2⦌)).symm_apply_apply B
      have hs : SSet.yonedaEquiv A = SSet.yonedaEquiv B :=
        CategoryTheory.nerve.eq_of_hornRestriction_eq
          (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
          (0 : Fin (k + 3)) hn
          ((congrArg
            (fun f : (Δ[k + 2] : SSet.{u}) ⟶ Y =>
              (SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫ f) hA).trans
            (hhorn.trans (congrArg
              (fun f : (Δ[k + 2] : SSet.{u}) ⟶ Y =>
                (SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫ f) hB.symm)))
      exact (SSet.yonedaEquiv (X := Y) (n := ⦋k + 2⦌)).injective hs

/-- The actual original unit sends a higher native relation map to its constant base object. -/
theorem nativeCoverUnit_relStructMap_eq_const
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} {f g : X.PtSimplex n x}
    (R : f.RelStruct₀ g) (hn : 2 ≤ n) :
    SSet.PtSimplex.RelStruct.map R ≫ nativeCoverUnit X =
      SSet.const (CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x)) := by
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let η : X ⟶ Y := nativeCoverUnit X
  let y : Y _⦋0⦌ := η.app (Opposite.op ⦋0⦌) x
  let A : (Δ[n + 1] : SSet.{u}) ⟶ Y := SSet.PtSimplex.RelStruct.map R ≫ η
  let B : (Δ[n + 1] : SSet.{u}) ⟶ Y := SSet.const y
  have hy : y = CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x) :=
    SSet.fundamentalGroupoidNerveEquiv_app_zero X (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) x
  have hg : SSet.RelativeMorphism.map g ≫ η =
      (SSet.const y : (Δ[n] : SSet.{u}) ⟶ Y) :=
    (SSet.PtSimplex.comp_fundamentalGroupoidNerveUnit_eq_const g hn).trans
      (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[n] : SSet.{u}) ⟶ Y)) hy.symm)
  have hface (j : Fin (n + 2)) (hj : j ≠ (0 : Fin (n + 2))) :
      SSet.stdSimplex.δ j ≫ A = SSet.stdSimplex.δ j ≫ B := by
    have ha : SSet.stdSimplex.δ j ≫ A =
        (SSet.const y : (Δ[n] : SSet.{u}) ⟶ Y) := by
      by_cases h1 : j = (0 : Fin (n + 1)).succ
      · subst j
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun v : (Δ[n] : SSet.{u}) ⟶ X => v ≫ η)
            (SSet.PtSimplex.RelStruct.δ_succ_map R)).trans hg)
      · have hj0 : j.val ≠ 0 := by
          intro hv
          apply hj
          apply Fin.ext
          simpa only [Fin.val_zero] using hv
        have hj1 : j.val ≠ 1 := by
          simpa only [Fin.ext_iff, Fin.val_succ, Fin.val_zero] using h1
        have hgt : (0 : Fin (n + 1)).succ < j := by
          have hgt_val : 1 < j.val := by omega
          simpa only [Fin.lt_def, Fin.val_succ, Fin.val_zero] using hgt_val
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun v : (Δ[n] : SSet.{u}) ⟶ X => v ≫ η)
            (SSet.PtSimplex.RelStruct.δ_map_of_gt R j hgt)).trans (SSet.const_comp x η))
    exact ha.trans (SSet.comp_const (SSet.stdSimplex.δ j) y).symm
  have hhorn : (SSet.horn (n + 1) (0 : Fin (n + 2))).ι ≫ A =
      (SSet.horn (n + 1) (0 : Fin (n + 2))).ι ≫ B := by
    apply SSet.horn.hom_ext'
    intro j hj
    simpa only [← Category.assoc, SSet.horn.ι_ι] using hface j hj
  have hA :
      (SSet.yonedaEquiv (X := Y) (n := ⦋n + 1⦌)).symm (SSet.yonedaEquiv A) = A :=
    (SSet.yonedaEquiv (X := Y) (n := ⦋n + 1⦌)).symm_apply_apply A
  have hB :
      (SSet.yonedaEquiv (X := Y) (n := ⦋n + 1⦌)).symm (SSet.yonedaEquiv B) = B :=
    (SSet.yonedaEquiv (X := Y) (n := ⦋n + 1⦌)).symm_apply_apply B
  have hs : SSet.yonedaEquiv A = SSet.yonedaEquiv B :=
    CategoryTheory.nerve.eq_of_hornRestriction_eq (SSet.FundamentalGroupoid X)
      (0 : Fin (n + 2)) (by omega)
      ((congrArg
        (fun v : (Δ[n + 1] : SSet.{u}) ⟶ Y => (SSet.horn (n + 1) (0 : Fin (n + 2))).ι ≫ v)
        hA).trans (hhorn.trans (congrArg
          (fun v : (Δ[n + 1] : SSet.{u}) ⟶ Y =>
            (SSet.horn (n + 1) (0 : Fin (n + 2))).ι ≫ v) hB.symm)))
  have hAB : A = B := (SSet.yonedaEquiv (X := Y) (n := ⦋n + 1⦌)).injective hs
  exact hAB.trans
    (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[n + 1] : SSet.{u}) ⟶ Y)) hy)

end SSet.KanComplex


namespace SSet.KanComplex

private theorem nativeCoverRelStructLiftSquare
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ} {f g : X.PtSimplex n x}
    (R : f.RelStruct₀ g) (hn : 2 ≤ n) :
    SSet.PtSimplex.RelStruct.map R ≫ nativeCoverUnit X =
      (SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) :
          (Δ[n + 1] : SSet.{u}) ⟶
            CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))) ≫
        nativeCoverNerveProjection X x := by
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let zU : U _⦋0⦌ :=
    ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))
  let q : U ⟶ Y := nativeCoverNerveProjection X x
  have hq0 : q.app (Opposite.op ⦋0⦌) zU =
      CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x) :=
    CategoryTheory.nerveMap_app_mk₀
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x))
      (CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x)))
  have hq : (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) ≫ q =
      (SSet.const (CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x)) :
        (Δ[n + 1] : SSet.{u}) ⟶ Y) :=
    (SSet.const_comp zU q).trans
      (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[n + 1] : SSet.{u}) ⟶ Y)) hq0)
  exact (nativeCoverUnit_relStructMap_eq_const R hn).trans hq.symm

/-- The actual original pullback map of a base relation and the constant identity path. -/
def nativeCoverRelStructLiftMap
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (τ υ : (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) υ))
    (hn : 2 ≤ n) : (Δ[n + 1] : SSet.{u}) ⟶ nativeCover X x :=
  pullback.lift (SSet.PtSimplex.RelStruct.map R)
    (SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))))
    (by exact nativeCoverRelStructLiftSquare R hn)

/-- Its first projection is the literal original relation map. -/
theorem nativeCoverRelStructLiftMap_projection
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (τ υ : (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) υ)) (hn : 2 ≤ n) :
    nativeCoverRelStructLiftMap τ υ R hn ≫ nativeCoverProjection X x =
      SSet.PtSimplex.RelStruct.map R := by
  dsimp only [nativeCoverRelStructLiftMap, nativeCoverProjection]
  exact pullback.lift_fst _ _ _

/-- Its second projection is the actual constant identity-path relation simplex. -/
theorem nativeCoverRelStructLiftMap_underProjection
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (τ υ : (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) υ)) (hn : 2 ≤ n) :
    nativeCoverRelStructLiftMap τ υ R hn ≫ nativeCoverUnderProjection X x =
      SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
  dsimp only [nativeCoverRelStructLiftMap, nativeCoverUnderProjection]
  exact pullback.lift_snd _ _ _

/-- Lift the actual base RelStruct₀ with its two original endpoints and all constant faces. -/
def nativeCoverRelStructLift
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (τ υ : (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) υ)) (hn : 2 ≤ n) : τ.RelStruct₀ υ where
  map := nativeCoverRelStructLiftMap τ υ R hn
  δ_castSucc_map := by
    apply nativeCover_hom_ext
    · have hτ :
          SSet.RelativeMorphism.map
            (SSet.PtSimplex.map (nativeCoverProjection X x)
              (nativeCoverProjection_identityPoint X x) τ) =
            SSet.RelativeMorphism.map τ ≫ nativeCoverProjection X x := rfl
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun v : (Δ[n + 1] : SSet.{u}) ⟶ X =>
            SSet.stdSimplex.δ (0 : Fin (n + 1)).castSucc ≫ v)
          (nativeCoverRelStructLiftMap_projection τ υ R hn)).trans
          ((SSet.PtSimplex.RelStruct.δ_castSucc_map R).trans hτ))
    · let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : nativeCover X x ⟶ U := nativeCoverUnderProjection X x
      have hL : nativeCoverRelStructLiftMap τ υ R hn ≫ r =
          (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) :=
        nativeCoverRelStructLiftMap_underProjection τ υ R hn
      have hc : SSet.stdSimplex.δ (0 : Fin (n + 1)).castSucc ≫
          (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) =
            (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.stdSimplex.δ (0 : Fin (n + 1)).castSucc) zU
      have he : SSet.RelativeMorphism.map τ ≫ r =
          (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        nativeCoverUnderProjection_pointedSimplex_eq_const τ hn
      have h : (SSet.stdSimplex.δ (0 : Fin (n + 1)).castSucc ≫
          nativeCoverRelStructLiftMap τ υ R hn) ≫ r =
            SSet.RelativeMorphism.map τ ≫ r :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun v : (Δ[n + 1] : SSet.{u}) ⟶ U =>
            SSet.stdSimplex.δ (0 : Fin (n + 1)).castSucc ≫ v) hL).trans
            (hc.trans he.symm))
      simpa only [U, r] using h
  δ_succ_map := by
    apply nativeCover_hom_ext
    · have hυ :
          SSet.RelativeMorphism.map
            (SSet.PtSimplex.map (nativeCoverProjection X x)
              (nativeCoverProjection_identityPoint X x) υ) =
            SSet.RelativeMorphism.map υ ≫ nativeCoverProjection X x := rfl
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun v : (Δ[n + 1] : SSet.{u}) ⟶ X =>
            SSet.stdSimplex.δ (0 : Fin (n + 1)).succ ≫ v)
          (nativeCoverRelStructLiftMap_projection τ υ R hn)).trans
          ((SSet.PtSimplex.RelStruct.δ_succ_map R).trans hυ))
    · let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : nativeCover X x ⟶ U := nativeCoverUnderProjection X x
      have hL : nativeCoverRelStructLiftMap τ υ R hn ≫ r =
          (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) :=
        nativeCoverRelStructLiftMap_underProjection τ υ R hn
      have hc : SSet.stdSimplex.δ (0 : Fin (n + 1)).succ ≫
          (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) =
            (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.stdSimplex.δ (0 : Fin (n + 1)).succ) zU
      have he : SSet.RelativeMorphism.map υ ≫ r =
          (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        nativeCoverUnderProjection_pointedSimplex_eq_const υ hn
      have h : (SSet.stdSimplex.δ (0 : Fin (n + 1)).succ ≫
          nativeCoverRelStructLiftMap τ υ R hn) ≫ r =
            SSet.RelativeMorphism.map υ ≫ r :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun v : (Δ[n + 1] : SSet.{u}) ⟶ U =>
            SSet.stdSimplex.δ (0 : Fin (n + 1)).succ ≫ v) hL).trans
            (hc.trans he.symm))
      simpa only [U, r] using h
  δ_map_of_lt j hj := by
    have hjv : j.val < 0 := by
      simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero] using hj
    exact (Nat.not_lt_zero j.val hjv).elim
  δ_map_of_gt j hj := by
    apply nativeCover_hom_ext
    · have hp :
          (SSet.const (nativeCoverIdentityPoint X x) :
            (Δ[n] : SSet.{u}) ⟶ nativeCover X x) ≫ nativeCoverProjection X x =
            SSet.const x :=
        (SSet.const_comp (nativeCoverIdentityPoint X x) (nativeCoverProjection X x)).trans
          (congrArg (fun z : X _⦋0⦌ => (SSet.const z : (Δ[n] : SSet.{u}) ⟶ X))
            (nativeCoverProjection_identityPoint X x))
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun v : (Δ[n + 1] : SSet.{u}) ⟶ X => SSet.stdSimplex.δ j ≫ v)
          (nativeCoverRelStructLiftMap_projection τ υ R hn)).trans
          ((SSet.PtSimplex.RelStruct.δ_map_of_gt R j hj).trans hp.symm))
    · let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : nativeCover X x ⟶ U := nativeCoverUnderProjection X x
      have hL : nativeCoverRelStructLiftMap τ υ R hn ≫ r =
          (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) :=
        nativeCoverRelStructLiftMap_underProjection τ υ R hn
      have hc : SSet.stdSimplex.δ j ≫ (SSet.const zU : (Δ[n + 1] : SSet.{u}) ⟶ U) =
          (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.stdSimplex.δ j) zU
      have hb : r.app (Opposite.op ⦋0⦌) (nativeCoverIdentityPoint X x) = zU :=
        nativeCoverUnderProjection_identityPoint X x
      have hr : (SSet.const (nativeCoverIdentityPoint X x) :
          (Δ[n] : SSet.{u}) ⟶ nativeCover X x) ≫ r =
            (SSet.const zU : (Δ[n] : SSet.{u}) ⟶ U) :=
        (SSet.const_comp (nativeCoverIdentityPoint X x) r).trans
          (congrArg (fun z : U _⦋0⦌ => (SSet.const z : (Δ[n] : SSet.{u}) ⟶ U)) hb)
      have h : (SSet.stdSimplex.δ j ≫ nativeCoverRelStructLiftMap τ υ R hn) ≫ r =
          (SSet.const (nativeCoverIdentityPoint X x) :
            (Δ[n] : SSet.{u}) ⟶ nativeCover X x) ≫ r :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun v : (Δ[n + 1] : SSet.{u}) ⟶ U =>
            SSet.stdSimplex.δ j ≫ v) hL).trans (hc.trans hr.symm))
      simpa only [U, r] using h

/-- The original lifted relation retains its actual underlying pullback map. -/
@[simp]
theorem nativeCoverRelStructLift_map
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (τ υ : (nativeCover X x).PtSimplex n (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) υ)) (hn : 2 ≤ n) :
    SSet.PtSimplex.RelStruct.map (nativeCoverRelStructLift τ υ R hn) =
      nativeCoverRelStructLiftMap τ υ R hn := rfl

/-- The actual original native π-map is injective in higher degrees of the given Kan complex. -/
theorem nativeCoverProjection_piMap_injective
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌} {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective
      (SSet.KanComplex.π.map (nativeCoverProjection X x)
        (nativeCoverProjection_identityPoint X x) n) := by
  let : SSet.KanComplex (nativeCover X x) := nativeCover_kanComplex X x
  intro a b hab
  obtain ⟨τ, rfl⟩ :=
    (SSet.KanComplex.π.mk_surjective
      (X := nativeCover X x) (x := nativeCoverIdentityPoint X x) (n := n)) a
  obtain ⟨υ, rfl⟩ :=
    (SSet.KanComplex.π.mk_surjective
      (X := nativeCover X x) (x := nativeCoverIdentityPoint X x) (n := n)) b
  have hbase :
      SSet.KanComplex.π.mk
        (SSet.PtSimplex.map (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) τ) =
        SSet.KanComplex.π.mk
          (SSet.PtSimplex.map (nativeCoverProjection X x)
            (nativeCoverProjection_identityPoint X x) υ) :=
    (SSet.KanComplex.π.map_mk (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).symm.trans
        (hab.trans (SSet.KanComplex.π.map_mk (nativeCoverProjection X x)
          (nativeCoverProjection_identityPoint X x) υ))
  obtain ⟨R⟩ :=
    (SSet.KanComplex.π.mk_eq_mk_iff (X := X) (x := x) (n := n)).mp hbase
  exact (SSet.KanComplex.π.mk_eq_mk_iff
    (X := nativeCover X x) (x := nativeCoverIdentityPoint X x) (n := n)).mpr
      ⟨nativeCoverRelStructLift τ υ R hn⟩

end SSet.KanComplex

namespace SSet.KanComplex

/-- The original projection is bijective on each native homotopy set in degree at least two. -/
theorem nativeCoverProjection_piMap_bijective
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌} {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective
      (SSet.KanComplex.π.map (nativeCoverProjection X x)
        (nativeCoverProjection_identityPoint X x) n) :=
  ⟨nativeCoverProjection_piMap_injective hn, nativeCoverProjection_piMap_surjective hn⟩

attribute [local instance] nativeCover_kanComplex

/-- The same original projection gives the native higher homotopy group equivalence. -/
noncomputable def nativeCoverProjectionPiMulEquiv
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌} (k : ℕ) (hk : 1 ≤ k) :
    SSet.KanComplex.π (k + 1) (nativeCover X x) (nativeCoverIdentityPoint X x) ≃*
      SSet.KanComplex.π (k + 1) X x :=
  MulEquiv.ofBijective
    (SSet.KanComplex.π.mapHom (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) k)
    (nativeCoverProjection_piMap_bijective (Nat.succ_le_succ hk))

/-- Deprecated alias for `nativeCoverProjectionPiMulEquiv`. -/
@[deprecated nativeCoverProjectionPiMulEquiv (since := "2026-10-28"),
  nolint defsWithUnderscore]
alias nativeCoverProjection_piMulEquiv := nativeCoverProjectionPiMulEquiv

/-- The constructed group equivalence retains the exact original native forward map. -/
@[simp]
theorem nativeCoverProjectionPiMulEquiv_apply
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌} (k : ℕ) (hk : 1 ≤ k)
    (a : SSet.KanComplex.π (k + 1) (nativeCover X x) (nativeCoverIdentityPoint X x)) :
    nativeCoverProjectionPiMulEquiv k hk a =
      SSet.KanComplex.π.map (nativeCoverProjection X x)
        (nativeCoverProjection_identityPoint X x) (k + 1) a := rfl

/-- Deprecated alias for `nativeCoverProjectionPiMulEquiv_apply`. -/
@[deprecated nativeCoverProjectionPiMulEquiv_apply (since := "2026-10-28")]
alias nativeCoverProjection_piMulEquiv_apply := nativeCoverProjectionPiMulEquiv_apply

end SSet.KanComplex
namespace SSet.KanComplex

/-- The two original projections satisfy the actual defining pullback equation. -/
private theorem nativeCoverProjection_condition
    {X : SSet.{u}} {x : X _⦋0⦌} :
    nativeCoverProjection X x ≫ nativeCoverUnit X =
      nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x := by
  dsimp only [nativeCover, nativeCoverProjection, nativeCoverUnderProjection] at *
  exact pullback.condition

/-- Every vertex of the original cover is reached by an actual edge from its identity point. -/
theorem nativeCover_exists_edge_from_identityPoint
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌}
    (v : (nativeCover X x) _⦋0⦌) :
    Nonempty ((nativeCover X x).Edge (nativeCoverIdentityPoint X x) v) := by
  classical
  let P : SSet.{u} := nativeCover X x
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ U := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let q : U ⟶ Y := nativeCoverNerveProjection X x
  let z : X _⦋0⦌ := p.app (Opposite.op ⦋0⦌) v
  let a : U _⦋0⦌ := r.app (Opposite.op ⦋0⦌) v
  let V : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) :=
    CategoryTheory.nerveEquiv a
  let U0 : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) :=
    CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x))
  let zU : U _⦋0⦌ := CategoryTheory.nerveEquiv.symm U0
  have ha : CategoryTheory.nerveEquiv.symm V = a :=
    (CategoryTheory.nerveEquiv
      (C := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))).symm_apply_apply a
  have hc : p ≫ η = r ≫ q := nativeCoverProjection_condition
  have hv : η.app (Opposite.op ⦋0⦌) z = q.app (Opposite.op ⦋0⦌) a := by
    change (p ≫ η).app (Opposite.op ⦋0⦌) v = (r ≫ q).app (Opposite.op ⦋0⦌) v
    exact congrArg (fun f : P ⟶ Y => f.app (Opposite.op ⦋0⦌) v) hc
  have hy : η.app (Opposite.op ⦋0⦌) z =
      CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk z) := by
    dsimp only [η, nativeCoverUnit]
    exact SSet.fundamentalGroupoidNerveEquiv_app_zero X (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) z
  have hqa : q.app (Opposite.op ⦋0⦌) a =
      q.app (Opposite.op ⦋0⦌) (CategoryTheory.nerveEquiv.symm V) :=
    congrArg (fun w : U _⦋0⦌ => q.app (Opposite.op ⦋0⦌) w) ha.symm
  have hqV : q.app (Opposite.op ⦋0⦌) (CategoryTheory.nerveEquiv.symm V) =
      CategoryTheory.nerveEquiv.symm V.right := by
    dsimp only [q, nativeCoverNerveProjection]
    exact CategoryTheory.nerveMap_app_mk₀
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x)) V
  have hq : q.app (Opposite.op ⦋0⦌) a = CategoryTheory.nerveEquiv.symm V.right :=
    hqa.trans hqV
  have κ : V.right = SSet.FundamentalGroupoid.mk z :=
    (CategoryTheory.nerveEquiv (C := SSet.FundamentalGroupoid X)).symm.injective
      (hq.symm.trans (hv.symm.trans hy))
  let γ : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z :=
    V.hom ≫ eqToHom κ
  obtain ⟨e, he⟩ := SSet.FundamentalGroupoid.homMk_surjective (X := X) (x := x) (y := z) γ
  let u : U0 ⟶ V := CategoryTheory.Under.homMk V.hom (by
    change (𝟙 (SSet.FundamentalGroupoid.mk x)) ≫ V.hom = V.hom
    exact Category.id_comp V.hom)
  let eu : U.Edge zU (CategoryTheory.nerveEquiv.symm V) := CategoryTheory.nerve.edgeMk u
  let eX : (Δ[1] : SSet.{u}) ⟶ X :=
    (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm e.edge
  let eU : (Δ[1] : SSet.{u}) ⟶ U :=
    (SSet.yonedaEquiv (X := U) (n := ⦋1⦌)).symm eu.edge
  have hx1 : η.app (Opposite.op ⦋1⦌) e.edge =
      (ComposableArrows.mk₁ V.hom : Y _⦋1⦌) := by
    have hid : η.app (Opposite.op ⦋1⦌) e.edge =
        (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) : Y _⦋1⦌) := by
      dsimp only [η, nativeCoverUnit]
      exact SSet.fundamentalGroupoidNerveEquiv_app_edge X (SSet.FundamentalGroupoid X)
        (𝟭 (SSet.FundamentalGroupoid X)) e
    have heγ : (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) : Y _⦋1⦌) =
        ComposableArrows.mk₁ γ :=
      congrArg
        (fun h : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z =>
          (ComposableArrows.mk₁ h : Y _⦋1⦌)) he
    have hγκ : (ComposableArrows.mk₁ γ : Y _⦋1⦌) = ComposableArrows.mk₁ V.hom :=
      ComposableArrows.mk₁_comp_eqToHom V.hom κ
    exact hid.trans (heγ.trans hγκ)
  have heU : eu.edge = (ComposableArrows.mk₁ u : U _⦋1⦌) :=
    CategoryTheory.nerve.edgeMk_edge u
  have hqu : q.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ u) =
      (ComposableArrows.mk₁
        ((CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x)).map u) : Y _⦋1⦌) := by
    dsimp only [q, nativeCoverNerveProjection]
    exact CategoryTheory.nerveMap_app_mk₁
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x)) u
  have hq1 : q.app (Opposite.op ⦋1⦌) eu.edge =
      (ComposableArrows.mk₁ V.hom : Y _⦋1⦌) :=
    (congrArg (fun w : U _⦋1⦌ => q.app (Opposite.op ⦋1⦌) w) heU).trans
      (hqu.trans (by rfl))
  have hcomm : eX ≫ η = eU ≫ q := by
    calc
      eX ≫ η = (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)).symm
          (η.app (Opposite.op ⦋1⦌) e.edge) := SSet.yonedaEquiv_symm_comp e.edge η
      _ = (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)).symm
          (ComposableArrows.mk₁ V.hom) :=
        congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)).symm hx1
      _ = (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)).symm
          (q.app (Opposite.op ⦋1⦌) eu.edge) :=
        congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)).symm hq1.symm
      _ = eU ≫ q := (SSet.yonedaEquiv_symm_comp eu.edge q).symm
  let L : (Δ[1] : SSet.{u}) ⟶ P := pullback.lift eX eU hcomm
  have hpL : L ≫ p = eX := by
    dsimp only [L, p, P, nativeCover, nativeCoverProjection]
    exact pullback.lift_fst _ _ _
  have hrL : L ≫ r = eU := by
    dsimp only [L, r, P, nativeCover, nativeCoverUnderProjection]
    exact pullback.lift_snd _ _ _
  have hpb : p.app (Opposite.op ⦋0⦌) b = x := nativeCoverProjection_identityPoint X x
  have hrb : r.app (Opposite.op ⦋0⦌) b = zU := nativeCoverUnderProjection_identityPoint X x
  have hsrcp : (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ p =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm b ≫ p := by
    calc
      (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ p =
          SSet.stdSimplex.δ (1 : Fin 2) ≫ (L ≫ p) := Category.assoc _ _ _
      _ = SSet.stdSimplex.δ (1 : Fin 2) ≫ eX :=
        congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ X => SSet.stdSimplex.δ (1 : Fin 2) ≫ f) hpL
      _ = (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm x :=
        SSet.Edge.δ_one_yonedaEquiv_symm e
      _ = (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm
          (p.app (Opposite.op ⦋0⦌) b) :=
        congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm hpb.symm
      _ = (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm b ≫ p :=
        (SSet.yonedaEquiv_symm_comp b p).symm
  have hsrcr : (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ r =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm b ≫ r := by
    calc
      (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ r =
          SSet.stdSimplex.δ (1 : Fin 2) ≫ (L ≫ r) := Category.assoc _ _ _
      _ = SSet.stdSimplex.δ (1 : Fin 2) ≫ eU :=
        congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ U => SSet.stdSimplex.δ (1 : Fin 2) ≫ f) hrL
      _ = (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm zU :=
        SSet.Edge.δ_one_yonedaEquiv_symm eu
      _ = (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm
          (r.app (Opposite.op ⦋0⦌) b) :=
        congrArg (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm hrb.symm
      _ = (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm b ≫ r :=
        (SSet.yonedaEquiv_symm_comp b r).symm
  have htgtp : (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ p =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm v ≫ p := by
    calc
      (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ p =
          SSet.stdSimplex.δ (0 : Fin 2) ≫ (L ≫ p) := Category.assoc _ _ _
      _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ eX :=
        congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ X => SSet.stdSimplex.δ (0 : Fin 2) ≫ f) hpL
      _ = (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm z :=
        SSet.Edge.δ_zero_yonedaEquiv_symm e
      _ = (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm v ≫ p :=
        (SSet.yonedaEquiv_symm_comp v p).symm
  have htgtr : (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ r =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm v ≫ r := by
    calc
      (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ r =
          SSet.stdSimplex.δ (0 : Fin 2) ≫ (L ≫ r) := Category.assoc _ _ _
      _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ eU :=
        congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ U => SSet.stdSimplex.δ (0 : Fin 2) ≫ f) hrL
      _ = (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm
          (CategoryTheory.nerveEquiv.symm V) := SSet.Edge.δ_zero_yonedaEquiv_symm eu
      _ = (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm a :=
        congrArg (SSet.yonedaEquiv (X := U) (n := ⦋0⦌)).symm ha
      _ = (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm v ≫ r :=
        (SSet.yonedaEquiv_symm_comp v r).symm
  have hs : SSet.stdSimplex.δ (1 : Fin 2) ≫ L =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm b :=
    nativeCover_hom_ext hsrcp hsrcr
  have ht : SSet.stdSimplex.δ (0 : Fin 2) ≫ L =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm v :=
    nativeCover_hom_ext htgtp htgtr
  refine ⟨SSet.Edge.mk (SSet.yonedaEquiv L) ?_ ?_⟩
  · exact (SSet.stdSimplex.yonedaEquiv_δ_comp L (1 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)) hs).trans
        ((SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).apply_symm_apply b))
  · exact (SSet.stdSimplex.yonedaEquiv_δ_comp L (0 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)) ht).trans
        ((SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).apply_symm_apply v))

/-- The original native cover is connected, with its actual identity-path point. -/
theorem nativeCover_isConnected
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌} :
    (nativeCover X x).IsConnected := by
  refine (SSet.isConnected_iff (X := nativeCover X x)).2 ⟨?_, ?_⟩
  · refine ⟨?_⟩
    intro a b
    obtain ⟨v, rfl⟩ := (SSet.π₀.mk_surjective (X := nativeCover X x)) a
    obtain ⟨w, rfl⟩ := (SSet.π₀.mk_surjective (X := nativeCover X x)) b
    obtain ⟨ev⟩ := nativeCover_exists_edge_from_identityPoint v
    obtain ⟨ew⟩ := nativeCover_exists_edge_from_identityPoint w
    exact (SSet.π₀.sound ev).symm.trans (SSet.π₀.sound ew)
  · exact ⟨nativeCoverIdentityPoint X x⟩

end SSet.KanComplex
namespace SSet.KanComplex

/-- An original pointed one-simplex projects to the identity loop in the Under nerve. -/
theorem nativeCoverUnderProjection_pointedOne_eq_const
    {X : SSet.{u}} {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)) :
    SSet.RelativeMorphism.map τ ≫ nativeCoverUnderProjection X x =
      SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
  let P : SSet.{u} := nativeCover X x
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
  let r : P ⟶ U := nativeCoverUnderProjection X x
  let U0 : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) :=
    CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x))
  let zU : U _⦋0⦌ := ComposableArrows.mk₀ U0
  have hrb : r.app (Opposite.op ⦋0⦌) b = zU :=
    nativeCoverUnderProjection_identityPoint X x
  let σ : U.PtSimplex 1 zU := SSet.PtSimplex.map r hrb τ
  have hσ : SSet.RelativeMorphism.map σ = SSet.RelativeMorphism.map τ ≫ r := rfl
  have hs : U.δ (1 : Fin 2) (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) = zU :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp
      (SSet.RelativeMorphism.map σ) (1 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := U) (n := ⦋0⦌))
        (SSet.PtSimplex.δ_map σ (1 : Fin 2))).trans (SSet.yonedaEquiv_const zU))
  have ht : U.δ (0 : Fin 2) (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) = zU :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp
      (SSet.RelativeMorphism.map σ) (0 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := U) (n := ⦋0⦌))
        (SSet.PtSimplex.δ_map σ (0 : Fin 2))).trans (SSet.yonedaEquiv_const zU))
  let e : U.Edge zU zU :=
    SSet.Edge.mk (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) hs ht
  have hz : CategoryTheory.nerveEquiv zU = U0 := rfl
  have hI : IsInitial (CategoryTheory.nerveEquiv zU) := by
    rw [hz]
    exact CategoryTheory.Under.mkIdInitial (X := SSet.FundamentalGroupoid.mk x)
  have hφ : CategoryTheory.nerve.homEquiv e =
      𝟙 (CategoryTheory.nerveEquiv zU) := hI.hom_ext _ _
  have hφid : CategoryTheory.nerve.homEquiv (SSet.Edge.id zU) =
      𝟙 (CategoryTheory.nerveEquiv zU) := CategoryTheory.nerve.homEquiv_id zU
  have heid : e = SSet.Edge.id zU :=
    (CategoryTheory.nerve.homEquiv
      (C := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      (x := zU) (y := zU)).injective (hφ.trans hφid.symm)
  have he : e.edge = SSet.yonedaEquiv (SSet.RelativeMorphism.map σ) :=
    SSet.Edge.mk_edge (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) hs ht
  have hc : SSet.yonedaEquiv (SSet.RelativeMorphism.map σ) =
      SSet.yonedaEquiv (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
    he.symm.trans
      ((congrArg (fun e' : U.Edge zU zU => e'.edge) heid).trans
        ((SSet.Edge.id_edge zU).trans (SSet.σ_zero_eq_yonedaEquiv_const zU)))
  have hmap : SSet.RelativeMorphism.map σ =
      (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
    (SSet.yonedaEquiv (X := U) (n := ⦋1⦌)).injective hc
  exact hσ.symm.trans hmap

end SSet.KanComplex
namespace SSet.KanComplex

/-- The actual projected based one-simplex has the native class of the constant loop. -/
theorem nativeCoverProjection_pointedOne_class_eq_const
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)) :
    SSet.KanComplex.π.mk (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ) =
        SSet.KanComplex.π.mk (SSet.RelativeMorphism.const : X.PtSimplex 1 x) := by
  let P : SSet.{u} := nativeCover X x
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let U : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ U := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let q : U ⟶ Y := nativeCoverNerveProjection X x
  let U0 : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) :=
    CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x))
  let zU : U _⦋0⦌ := ComposableArrows.mk₀ U0
  let zY : Y _⦋0⦌ := CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x)
  have hp : p.app (Opposite.op ⦋0⦌) b = x := nativeCoverProjection_identityPoint X x
  let σ : X.PtSimplex 1 x := SSet.PtSimplex.map p hp τ
  let c : X.PtSimplex 1 x := SSet.RelativeMorphism.const
  have hσ : SSet.RelativeMorphism.map σ = SSet.RelativeMorphism.map τ ≫ p := rfl
  have hc : SSet.RelativeMorphism.map c = (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) := rfl
  have hU : SSet.RelativeMorphism.map τ ≫ r =
      (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
    nativeCoverUnderProjection_pointedOne_eq_const τ
  have hpq : p ≫ η = r ≫ q := nativeCoverProjection_condition
  have hq0 : q.app (Opposite.op ⦋0⦌) zU = zY := by
    dsimp only [q, nativeCoverNerveProjection]
    exact CategoryTheory.nerveMap_app_mk₀
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x)) U0
  have hΓ : SSet.RelativeMorphism.map σ ≫ η =
      (SSet.const zY : (Δ[1] : SSet.{u}) ⟶ Y) := by
    calc
      SSet.RelativeMorphism.map σ ≫ η = (SSet.RelativeMorphism.map τ ≫ p) ≫ η :=
        congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ X => f ≫ η) hσ
      _ = SSet.RelativeMorphism.map τ ≫ (p ≫ η) := Category.assoc _ _ _
      _ = SSet.RelativeMorphism.map τ ≫ (r ≫ q) :=
        congrArg (fun f : P ⟶ Y => SSet.RelativeMorphism.map τ ≫ f) hpq
      _ = (SSet.RelativeMorphism.map τ ≫ r) ≫ q := (Category.assoc _ _ _).symm
      _ = (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) ≫ q :=
        congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ U => f ≫ q) hU
      _ = SSet.const (q.app (Opposite.op ⦋0⦌) zU) := SSet.const_comp zU q
      _ = SSet.const zY :=
        congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[1] : SSet.{u}) ⟶ Y)) hq0
  have hs : X.δ (1 : Fin 2) (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) = x :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp
      (SSet.RelativeMorphism.map σ) (1 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        (SSet.PtSimplex.δ_map σ (1 : Fin 2))).trans (SSet.yonedaEquiv_const x))
  have ht : X.δ (0 : Fin 2) (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) = x :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp
      (SSet.RelativeMorphism.map σ) (0 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        (SSet.PtSimplex.δ_map σ (0 : Fin 2))).trans (SSet.yonedaEquiv_const x))
  let e : X.Edge x x :=
    SSet.Edge.mk (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) hs ht
  have he : e.edge = SSet.yonedaEquiv (SSet.RelativeMorphism.map σ) :=
    SSet.Edge.mk_edge (SSet.yonedaEquiv (SSet.RelativeMorphism.map σ)) hs ht
  have hη : η.app (Opposite.op ⦋1⦌) e.edge =
      (ComposableArrows.mk₁ (𝟙 (SSet.FundamentalGroupoid.mk x)) : Y _⦋1⦌) := by
    have heval : (η.app (Opposite.op ⦋1⦌) e.edge : Y _⦋1⦌) =
        η.app (Opposite.op ⦋1⦌)
          ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)) (SSet.RelativeMorphism.map σ)) :=
      congrArg (fun z : X _⦋1⦌ => (η.app (Opposite.op ⦋1⦌) z : Y _⦋1⦌)) he
    have hnat : (η.app (Opposite.op ⦋1⦌)
        ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌))
          (SSet.RelativeMorphism.map σ)) : Y _⦋1⦌) =
        (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)) (SSet.RelativeMorphism.map σ ≫ η) :=
      (SSet.yonedaEquiv_comp (SSet.RelativeMorphism.map σ) η).symm
    have hconst : ((SSet.yonedaEquiv (X := Y) (n := ⦋1⦌))
        (SSet.RelativeMorphism.map σ ≫ η) : Y _⦋1⦌) =
        (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌))
          (SSet.const zY : (Δ[1] : SSet.{u}) ⟶ Y) :=
      congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)) hΓ
    have hdeg : ((SSet.yonedaEquiv (X := Y) (n := ⦋1⦌))
        (SSet.const zY : (Δ[1] : SSet.{u}) ⟶ Y) : Y _⦋1⦌) = Y.σ 0 zY :=
      (SSet.σ_zero_eq_yonedaEquiv_const (X := Y) zY).symm
    have hnerve : (Y.σ (0 : Fin 1) zY : Y _⦋1⦌) =
        (ComposableArrows.mk₁ (𝟙 (SSet.FundamentalGroupoid.mk x)) : Y _⦋1⦌) := by
      dsimp only [Y, zY]
      exact CategoryTheory.nerve.σ_zero_nerveEquiv_symm (SSet.FundamentalGroupoid.mk x)
    exact heval.trans (hnat.trans (hconst.trans (hdeg.trans hnerve)))
  have hηe : η.app (Opposite.op ⦋1⦌) e.edge =
      (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) : Y _⦋1⦌) := by
    dsimp only [η, nativeCoverUnit]
    exact SSet.fundamentalGroupoidNerveEquiv_app_edge X (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) e
  have hmk : (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) : Y _⦋1⦌) =
      ComposableArrows.mk₁ (𝟙 (SSet.FundamentalGroupoid.mk x)) := hηe.symm.trans hη
  have hloop : SSet.FundamentalGroupoid.homMk e =
      𝟙 (SSet.FundamentalGroupoid.mk x) := by
    let d : (0 : Fin 2) ⟶ (1 : Fin 2) := homOfLE (by decide)
    have hd := CategoryTheory.Functor.congr_hom hmk d
    simpa only [ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
      ComposableArrows.Mk₁.map, eqToHom_refl, Category.id_comp, Category.comp_id] using hd
  have hs0 : X.δ (1 : Fin 2) (SSet.yonedaEquiv (SSet.RelativeMorphism.map c)) = x :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp
      (SSet.RelativeMorphism.map c) (1 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        (SSet.PtSimplex.δ_map c (1 : Fin 2))).trans (SSet.yonedaEquiv_const x))
  have ht0 : X.δ (0 : Fin 2) (SSet.yonedaEquiv (SSet.RelativeMorphism.map c)) = x :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp
      (SSet.RelativeMorphism.map c) (0 : Fin 2)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌))
        (SSet.PtSimplex.δ_map c (0 : Fin 2))).trans (SSet.yonedaEquiv_const x))
  let e0 : X.Edge x x :=
    SSet.Edge.mk (SSet.yonedaEquiv (SSet.RelativeMorphism.map c)) hs0 ht0
  have he0raw : e0.edge = (SSet.Edge.id x).edge :=
    (SSet.Edge.mk_edge (SSet.yonedaEquiv (SSet.RelativeMorphism.map c)) hs0 ht0).trans
      ((congrArg (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)) hc).trans
        ((SSet.σ_zero_eq_yonedaEquiv_const x).symm.trans (SSet.Edge.id_edge x).symm))
  have he0 : e0 = SSet.Edge.id x := SSet.Edge.ext he0raw
  have hloop0 : SSet.FundamentalGroupoid.homMk e0 =
      𝟙 (SSet.FundamentalGroupoid.mk x) :=
    (congrArg (fun f : X.Edge x x => SSet.FundamentalGroupoid.homMk f) he0).trans
      (SSet.FundamentalGroupoid.homMk_id x)
  let φ : SSet.KanComplex.π 1 X x ≃* End (SSet.FundamentalGroupoid.mk x) :=
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd (X := X) x
  have hφ : φ (SSet.KanComplex.π.mk σ) =
      End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk e)) := by
    simpa only [φ, e] using
      (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk (X := X) x σ)
  have hφ0 : φ (SSet.KanComplex.π.mk c) =
      End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk e0)) := by
    simpa only [φ, e0] using
      (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk (X := X) x c)
  change SSet.KanComplex.π.mk σ = SSet.KanComplex.π.mk c
  apply φ.injective
  calc
    φ (SSet.KanComplex.π.mk σ) =
        End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk e)) := hφ
    _ = End.of (CategoryTheory.inv (𝟙 (SSet.FundamentalGroupoid.mk x))) :=
      congrArg (fun f : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk x =>
        End.of (CategoryTheory.inv f)) hloop
    _ = End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk e0)) :=
      (congrArg
        (fun f : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk x =>
          End.of (CategoryTheory.inv f)) hloop0).symm
    _ = φ (SSet.KanComplex.π.mk c) := hφ0.symm

end SSet.KanComplex
namespace SSet.KanComplex

/-- The original unit sends a native one-relation to the constant base object
when its right endpoint is the actual pointed constant loop. -/
theorem nativeCoverUnit_relStructOneMap_eq_const
    {X : SSet.{u}} {x : X _⦋0⦌} {f : X.PtSimplex 1 x}
    (R : f.RelStruct₀ (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    SSet.PtSimplex.RelStruct.map R ≫ nativeCoverUnit X =
      SSet.const (CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x)) := by
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let η : X ⟶ Y := nativeCoverUnit X
  let y : Y _⦋0⦌ := η.app (Opposite.op ⦋0⦌) x
  let A : (Δ[2] : SSet.{u}) ⟶ Y := SSet.PtSimplex.RelStruct.map R ≫ η
  let B : (Δ[2] : SSet.{u}) ⟶ Y := SSet.const y
  have hy : y = CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x) :=
    SSet.fundamentalGroupoidNerveEquiv_app_zero X (SSet.FundamentalGroupoid X)
      (𝟭 (SSet.FundamentalGroupoid X)) x
  have hg :
      SSet.RelativeMorphism.map (SSet.RelativeMorphism.const : X.PtSimplex 1 x) =
        (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) := rfl
  have hδ1 : SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.PtSimplex.RelStruct.map R =
      (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) :=
    (SSet.PtSimplex.RelStruct.δ_succ_map R).trans hg
  have hδ2 : SSet.stdSimplex.δ (2 : Fin 3) ≫ SSet.PtSimplex.RelStruct.map R =
      (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) :=
    SSet.PtSimplex.RelStruct.δ_map_of_gt R (2 : Fin 3) (by decide)
  have hface1 : SSet.stdSimplex.δ (1 : Fin 3) ≫ A =
      SSet.stdSimplex.δ (1 : Fin 3) ≫ B :=
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun v : (Δ[1] : SSet.{u}) ⟶ X => v ≫ η) hδ1).trans
        (SSet.const_comp x η))).trans
      (SSet.comp_const (SSet.stdSimplex.δ (1 : Fin 3)) y).symm
  have hface2 : SSet.stdSimplex.δ (2 : Fin 3) ≫ A =
      SSet.stdSimplex.δ (2 : Fin 3) ≫ B :=
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun v : (Δ[1] : SSet.{u}) ⟶ X => v ≫ η) hδ2).trans
        (SSet.const_comp x η))).trans
      (SSet.comp_const (SSet.stdSimplex.δ (2 : Fin 3)) y).symm
  have hface (j : Fin 3) (hj : j ≠ (0 : Fin 3)) :
      SSet.stdSimplex.δ j ≫ A = SSet.stdSimplex.δ j ≫ B := by
    by_cases h1 : j = (1 : Fin 3)
    · subst j
      exact hface1
    · have h2 : j = (2 : Fin 3) := by
        apply Fin.ext
        have hj0 : j.val ≠ 0 := by
          intro hv
          apply hj
          apply Fin.ext
          simpa only [Fin.val_zero] using hv
        have hj1 : j.val ≠ 1 := by
          intro hv
          apply h1
          apply Fin.ext
          simpa only [Fin.val_one] using hv
        have hjlt : j.val < 3 := j.isLt
        have hval : j.val = 2 := by omega
        have hval2 : (2 : Fin 3).val = 2 := by decide
        exact hval.trans hval2.symm
      subst j
      exact hface2
  have hhorn : (SSet.horn 2 (0 : Fin 3)).ι ≫ A =
      (SSet.horn 2 (0 : Fin 3)).ι ≫ B := by
    apply SSet.horn.hom_ext'
    intro j hj
    simpa only [← Category.assoc, SSet.horn.ι_ι] using hface j hj
  have hA :
      (SSet.yonedaEquiv (X := Y) (n := ⦋2⦌)).symm (SSet.yonedaEquiv A) = A :=
    (SSet.yonedaEquiv (X := Y) (n := ⦋2⦌)).symm_apply_apply A
  have hB :
      (SSet.yonedaEquiv (X := Y) (n := ⦋2⦌)).symm (SSet.yonedaEquiv B) = B :=
    (SSet.yonedaEquiv (X := Y) (n := ⦋2⦌)).symm_apply_apply B
  have hs : SSet.yonedaEquiv A = SSet.yonedaEquiv B :=
    CategoryTheory.nerve.eq_of_hornRestriction_eq (SSet.FundamentalGroupoid X)
      (0 : Fin 3) (by decide)
      ((congrArg
        (fun v : (Δ[2] : SSet.{u}) ⟶ Y => (SSet.horn 2 (0 : Fin 3)).ι ≫ v)
        hA).trans (hhorn.trans (congrArg
          (fun v : (Δ[2] : SSet.{u}) ⟶ Y => (SSet.horn 2 (0 : Fin 3)).ι ≫ v)
          hB.symm)))
  have hAB : A = B := (SSet.yonedaEquiv (X := Y) (n := ⦋2⦌)).injective hs
  exact hAB.trans
    (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[2] : SSet.{u}) ⟶ Y)) hy)

end SSet.KanComplex
namespace SSet.KanComplex

/-- The original pullback map of a projected one-relation to the constant loop
and the constant identity-path simplex. -/
def nativeCoverRelStructOneLiftMap
    {X : SSet.{u}} {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    (Δ[2] : SSet.{u}) ⟶ nativeCover X x :=
  pullback.lift (SSet.PtSimplex.RelStruct.map R)
    (SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
      (𝟙 (SSet.FundamentalGroupoid.mk x)))))
    (by
      let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
      let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let q : U ⟶ Y := nativeCoverNerveProjection X x
      have hq0 : q.app (Opposite.op ⦋0⦌) zU =
          CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x) :=
        CategoryTheory.nerveMap_app_mk₀
          (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x))
          (CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x)))
      have hq : (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) ≫ q =
          (SSet.const (CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk x)) :
            (Δ[2] : SSet.{u}) ⟶ Y) :=
        (SSet.const_comp zU q).trans
          (congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[2] : SSet.{u}) ⟶ Y)) hq0)
      exact (nativeCoverUnit_relStructOneMap_eq_const R).trans hq.symm)

/-- Its original first projection is the literal base relation map. -/
theorem nativeCoverRelStructOneLiftMap_projection
    {X : SSet.{u}} {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    nativeCoverRelStructOneLiftMap τ R ≫ nativeCoverProjection X x =
      SSet.PtSimplex.RelStruct.map R := by
  dsimp only [nativeCoverRelStructOneLiftMap, nativeCoverProjection]
  exact pullback.lift_fst _ _ _

/-- Its original second projection is the constant identity-path simplex. -/
theorem nativeCoverRelStructOneLiftMap_underProjection
    {X : SSet.{u}} {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    nativeCoverRelStructOneLiftMap τ R ≫ nativeCoverUnderProjection X x =
      SSet.const (ComposableArrows.mk₀ (CategoryTheory.Under.mk
        (𝟙 (SSet.FundamentalGroupoid.mk x)))) := by
  dsimp only [nativeCoverRelStructOneLiftMap, nativeCoverUnderProjection]
  exact pullback.lift_snd _ _ _

end SSet.KanComplex
namespace SSet.KanComplex

/-- Lift the actual projected one-relation to a relation from the original
pointed loop to the actual constant loop at the identity-path point. -/
def nativeCoverRelStructOneLift
    {X : SSet.{u}} {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x))
    (R : (SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ).RelStruct₀
        (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    τ.RelStruct₀ (SSet.RelativeMorphism.const :
      (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)) where
  map := nativeCoverRelStructOneLiftMap τ R
  δ_castSucc_map := by
    apply nativeCover_hom_ext
    · have hτ :
          SSet.RelativeMorphism.map
            (SSet.PtSimplex.map (nativeCoverProjection X x)
              (nativeCoverProjection_identityPoint X x) τ) =
            SSet.RelativeMorphism.map τ ≫ nativeCoverProjection X x := rfl
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun v : (Δ[2] : SSet.{u}) ⟶ X =>
            SSet.stdSimplex.δ (0 : Fin 2).castSucc ≫ v)
          (nativeCoverRelStructOneLiftMap_projection τ R)).trans
          ((SSet.PtSimplex.RelStruct.δ_castSucc_map R).trans hτ))
    · let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : nativeCover X x ⟶ U := nativeCoverUnderProjection X x
      have hL : nativeCoverRelStructOneLiftMap τ R ≫ r =
          (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) :=
        nativeCoverRelStructOneLiftMap_underProjection τ R
      have hc : SSet.stdSimplex.δ (0 : Fin 2).castSucc ≫
          (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) =
            (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.stdSimplex.δ (0 : Fin 2).castSucc) zU
      have he : SSet.RelativeMorphism.map τ ≫ r =
          (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
        nativeCoverUnderProjection_pointedOne_eq_const τ
      have h : (SSet.stdSimplex.δ (0 : Fin 2).castSucc ≫
          nativeCoverRelStructOneLiftMap τ R) ≫ r =
            SSet.RelativeMorphism.map τ ≫ r :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun v : (Δ[2] : SSet.{u}) ⟶ U =>
            SSet.stdSimplex.δ (0 : Fin 2).castSucc ≫ v) hL).trans
            (hc.trans he.symm))
      simpa only [U, r] using h
  δ_succ_map := by
    have hconstP : SSet.RelativeMorphism.map (SSet.RelativeMorphism.const :
        (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)) =
          (SSet.const (nativeCoverIdentityPoint X x) :
            (Δ[1] : SSet.{u}) ⟶ nativeCover X x) := rfl
    rw [hconstP]
    apply nativeCover_hom_ext
    · have hconstX :
          SSet.RelativeMorphism.map (SSet.RelativeMorphism.const : X.PtSimplex 1 x) =
            (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) := rfl
      have hp :
          (SSet.const (nativeCoverIdentityPoint X x) :
            (Δ[1] : SSet.{u}) ⟶ nativeCover X x) ≫ nativeCoverProjection X x =
            (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) :=
        (SSet.const_comp (nativeCoverIdentityPoint X x) (nativeCoverProjection X x)).trans
          (congrArg (fun z : X _⦋0⦌ => (SSet.const z : (Δ[1] : SSet.{u}) ⟶ X))
            (nativeCoverProjection_identityPoint X x))
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun v : (Δ[2] : SSet.{u}) ⟶ X =>
            SSet.stdSimplex.δ (0 : Fin 2).succ ≫ v)
          (nativeCoverRelStructOneLiftMap_projection τ R)).trans
          ((SSet.PtSimplex.RelStruct.δ_succ_map R).trans (hconstX.trans hp.symm)))
    · let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : nativeCover X x ⟶ U := nativeCoverUnderProjection X x
      have hL : nativeCoverRelStructOneLiftMap τ R ≫ r =
          (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) :=
        nativeCoverRelStructOneLiftMap_underProjection τ R
      have hc : SSet.stdSimplex.δ (0 : Fin 2).succ ≫
          (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) =
            (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.stdSimplex.δ (0 : Fin 2).succ) zU
      have hb : r.app (Opposite.op ⦋0⦌) (nativeCoverIdentityPoint X x) = zU :=
        nativeCoverUnderProjection_identityPoint X x
      have hr : (SSet.const (nativeCoverIdentityPoint X x) :
          (Δ[1] : SSet.{u}) ⟶ nativeCover X x) ≫ r =
            (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
        (SSet.const_comp (nativeCoverIdentityPoint X x) r).trans
          (congrArg (fun z : U _⦋0⦌ => (SSet.const z : (Δ[1] : SSet.{u}) ⟶ U)) hb)
      have h : (SSet.stdSimplex.δ (0 : Fin 2).succ ≫
          nativeCoverRelStructOneLiftMap τ R) ≫ r =
            (SSet.const (nativeCoverIdentityPoint X x) :
              (Δ[1] : SSet.{u}) ⟶ nativeCover X x) ≫ r :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun v : (Δ[2] : SSet.{u}) ⟶ U =>
            SSet.stdSimplex.δ (0 : Fin 2).succ ≫ v) hL).trans (hc.trans hr.symm))
      simpa only [U, r] using h
  δ_map_of_lt j hj := by
    have hjv : j.val < 0 := by
      simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero] using hj
    exact (Nat.not_lt_zero j.val hjv).elim
  δ_map_of_gt j hj := by
    apply nativeCover_hom_ext
    · have hp :
          (SSet.const (nativeCoverIdentityPoint X x) :
            (Δ[1] : SSet.{u}) ⟶ nativeCover X x) ≫ nativeCoverProjection X x =
            (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) :=
        (SSet.const_comp (nativeCoverIdentityPoint X x) (nativeCoverProjection X x)).trans
          (congrArg (fun z : X _⦋0⦌ => (SSet.const z : (Δ[1] : SSet.{u}) ⟶ X))
            (nativeCoverProjection_identityPoint X x))
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun v : (Δ[2] : SSet.{u}) ⟶ X => SSet.stdSimplex.δ j ≫ v)
          (nativeCoverRelStructOneLiftMap_projection τ R)).trans
          ((SSet.PtSimplex.RelStruct.δ_map_of_gt R j hj).trans hp.symm))
    · let U : SSet.{u} :=
        CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      let zU : U _⦋0⦌ :=
        ComposableArrows.mk₀ (CategoryTheory.Under.mk
          (𝟙 (SSet.FundamentalGroupoid.mk x)))
      let r : nativeCover X x ⟶ U := nativeCoverUnderProjection X x
      have hL : nativeCoverRelStructOneLiftMap τ R ≫ r =
          (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) :=
        nativeCoverRelStructOneLiftMap_underProjection τ R
      have hc : SSet.stdSimplex.δ j ≫ (SSet.const zU : (Δ[2] : SSet.{u}) ⟶ U) =
          (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
        SSet.comp_const (SSet.stdSimplex.δ j) zU
      have hb : r.app (Opposite.op ⦋0⦌) (nativeCoverIdentityPoint X x) = zU :=
        nativeCoverUnderProjection_identityPoint X x
      have hr : (SSet.const (nativeCoverIdentityPoint X x) :
          (Δ[1] : SSet.{u}) ⟶ nativeCover X x) ≫ r =
            (SSet.const zU : (Δ[1] : SSet.{u}) ⟶ U) :=
        (SSet.const_comp (nativeCoverIdentityPoint X x) r).trans
          (congrArg (fun z : U _⦋0⦌ => (SSet.const z : (Δ[1] : SSet.{u}) ⟶ U)) hb)
      have h : (SSet.stdSimplex.δ j ≫ nativeCoverRelStructOneLiftMap τ R) ≫ r =
          (SSet.const (nativeCoverIdentityPoint X x) :
            (Δ[1] : SSet.{u}) ⟶ nativeCover X x) ≫ r :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun v : (Δ[2] : SSet.{u}) ⟶ U =>
            SSet.stdSimplex.δ j ≫ v) hL).trans (hc.trans hr.symm))
      simpa only [U, r] using h

end SSet.KanComplex
namespace SSet.KanComplex

/-- Every original pointed cover loop has the actual constant native class. -/
theorem nativeCover_piOne_mk_eq_const
    {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}
    (τ : (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)) :
    π.mk τ = π.mk (SSet.RelativeMorphism.const :
      (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)) := by
  have hbase :
      π.mk (SSet.PtSimplex.map (nativeCoverProjection X x)
        (nativeCoverProjection_identityPoint X x) τ) =
          π.mk (SSet.RelativeMorphism.const : X.PtSimplex 1 x) :=
    nativeCoverProjection_pointedOne_class_eq_const τ
  obtain ⟨R⟩ := (π.mk_eq_mk_iff (X := X)
    (p := SSet.PtSimplex.map (nativeCoverProjection X x)
      (nativeCoverProjection_identityPoint X x) τ)
    (q := (SSet.RelativeMorphism.const : X.PtSimplex 1 x))).mp hbase
  let : KanComplex (nativeCover X x) := nativeCover_kanComplex X x
  exact (π.mk_eq_mk_iff (X := nativeCover X x)
    (p := τ) (q := (SSet.RelativeMorphism.const :
      (nativeCover X x).PtSimplex 1 (nativeCoverIdentityPoint X x)))).mpr
      ⟨nativeCoverRelStructOneLift τ R⟩

/-- The native fundamental group at the original identity-path point is trivial. -/
theorem nativeCover_piOne_subsingleton
    {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} :
    Subsingleton (π 1 (nativeCover X x) (nativeCoverIdentityPoint X x)) := by
  refine ⟨fun a₁ a₂ => ?_⟩
  obtain ⟨τ, rfl⟩ := π.mk_surjective a₁
  obtain ⟨υ, rfl⟩ := π.mk_surjective a₂
  exact (nativeCover_piOne_mk_eq_const τ).trans
    (nativeCover_piOne_mk_eq_const υ).symm

end SSet.KanComplex
namespace SSet.KanComplex

/-- The original native cover is connected and has trivial native fundamental
group at every original vertex. -/
theorem nativeCover_isConnected_and_piOne_subsingleton
    {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} :
    (nativeCover X x).IsConnected ∧
      ∀ v : (nativeCover X x) _⦋0⦌, Subsingleton (π 1 (nativeCover X x) v) := by
  refine ⟨nativeCover_isConnected (X := X) (x := x), ?_⟩
  intro v
  let : KanComplex (nativeCover X x) := nativeCover_kanComplex X x
  obtain ⟨e⟩ := nativeCover_exists_edge_from_identityPoint (X := X) (x := x) v
  let A : π 1 (nativeCover X x) (nativeCoverIdentityPoint X x) ≃
      π 1 (nativeCover X x) v :=
    π.actionEquiv (X := nativeCover X x) (n := 1) (SSet.FundamentalGroupoid.homMk e)
  let : Subsingleton (π 1 (nativeCover X x) (nativeCoverIdentityPoint X x)) :=
    nativeCover_piOne_subsingleton (X := X) (x := x)
  refine ⟨fun a₁ a₂ => ?_⟩
  apply A.symm.injective
  exact Subsingleton.elim (A.symm a₁) (A.symm a₂)

end SSet.KanComplex
namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] (y : C)

/-- Strict endpoint equality and the projection equation determine the lifted object. -/
theorem lift_object_unique (U : Under y) {z : C} (g : U.right ⟶ z)
    (V : Under y) (hV : V.right = z) (f : U ⟶ V)
    (hf : f.right ≫ eqToHom hV = g) :
    V = Under.mk (U.hom ≫ g) := by
  apply StructuredArrow.obj_ext V (Under.mk (U.hom ≫ g)) hV
  change V.hom ≫ eqToHom hV = U.hom ≫ g
  rw [← Under.w f, Category.assoc, hf]

end CategoryTheory.Under
namespace CategoryTheory.Under

/-- The original Under projection has a unique one-simplex lift from a fixed
first object over the given base arrow. -/
theorem existsUnique_oneSimplexLift_from
    {C : Type u} [Category.{v} C] (y : C) (U : Under y) {z : C}
    (g : U.right ⟶ z) :
    ∃! s : ComposableArrows (Under y) 1,
      ((Under.forget y).mapComposableArrows 1).obj s = ComposableArrows.mk₁ g ∧
        s.left = U := by
  let V₀ : Under y := Under.mk (U.hom ≫ g)
  let f₀ : U ⟶ V₀ := Under.homMk g rfl
  let s₀ : ComposableArrows (Under y) 1 := ComposableArrows.mk₁ f₀
  refine ⟨s₀, ⟨?_, rfl⟩, ?_⟩
  · refine ComposableArrows.ext₁
      (F := ((Under.forget y).mapComposableArrows 1).obj s₀)
      (G := ComposableArrows.mk₁ g) rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro s hs
    let f : U ⟶ s.right := eqToHom hs.2.symm ≫ s.hom
    have hsource : ComposableArrows.mk₁ f = s :=
      (ComposableArrows.mk₁_eqToHom_comp hs.2.symm s.hom).trans
        (ComposableArrows.mk₁_hom s)
    have hmap : ((Under.forget y).mapComposableArrows 1).obj
        (ComposableArrows.mk₁ f) = ComposableArrows.mk₁ f.right := by
      refine ComposableArrows.ext₁
        (F := ((Under.forget y).mapComposableArrows 1).obj (ComposableArrows.mk₁ f))
        (G := ComposableArrows.mk₁ f.right) rfl rfl ?_
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    have hbase : ComposableArrows.mk₁ f.right = ComposableArrows.mk₁ g :=
      hmap.symm.trans
        ((congrArg (fun t : ComposableArrows (Under y) 1 =>
          ((Under.forget y).mapComposableArrows 1).obj t) hsource).trans hs.1)
    let κ : s.right.right = z :=
      congrArg (fun t : ComposableArrows C 1 => t.right) hbase
    let d : (0 : Fin 2) ⟶ (1 : Fin 2) := homOfLE (by decide)
    have hright : f.right = g ≫ eqToHom κ.symm := by
      simpa only [ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
        ComposableArrows.Mk₁.map, eqToHom_refl, Category.id_comp] using
          (Functor.congr_hom hbase d)
    have hprojection : f.right ≫ eqToHom κ = g := by
      have h := congrArg (fun a : U.right ⟶ s.right.right => a ≫ eqToHom κ) hright
      simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h
    have htarget : s.right = V₀ :=
      lift_object_unique y U g s.right κ f hprojection
    have hcanonical : f ≫ eqToHom htarget = f₀ := by
      apply (Under.forget y).map_injective
      simpa only [Under.forget_map, Under.comp_right, Under.eqToHom_right,
        V₀, f₀, Under.homMk_right] using hprojection
    exact hsource.symm.trans
      ((ComposableArrows.mk₁_comp_eqToHom f htarget).symm.trans
        (congrArg (fun a : U ⟶ V₀ => ComposableArrows.mk₁ a) hcanonical))

end CategoryTheory.Under
namespace CategoryTheory.Under

/-- The original Under simplex built from a prescribed first object and its
actual endpoint equality over the given base simplex. -/
def simplexLiftFromFirst
    {C : Type u} [Category.{v} C] (y : C) {n : ℕ}
    (σ : ComposableArrows C n) (U : Under y) (κ : U.right = σ.left) :
    ComposableArrows (Under y) n :=
  let i₀ : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  Under.lift σ
    { app j := U.hom ≫ eqToHom κ ≫
        σ.map (homOfLE (show i₀ ≤ j from Nat.zero_le j.val))
      naturality {i j} f := by
        have h : (homOfLE (show i₀ ≤ i from Nat.zero_le i.val) : i₀ ⟶ i) ≫ f =
            homOfLE (show i₀ ≤ j from Nat.zero_le j.val) :=
          Subsingleton.elim _ _
        have hm : σ.map (homOfLE (show i₀ ≤ i from Nat.zero_le i.val)) ≫ σ.map f =
            σ.map (homOfLE (show i₀ ≤ j from Nat.zero_le j.val)) :=
          (σ.map_comp (homOfLE (show i₀ ≤ i from Nat.zero_le i.val)) f).symm.trans
            (congrArg (fun a : i₀ ⟶ j => σ.map a) h)
        dsimp
        refine (Category.id_comp _).trans ?_
        exact (congrArg (fun a : σ.obj i₀ ⟶ σ.obj j => U.hom ≫ eqToHom κ ≫ a)
          hm.symm).trans
          ((congrArg (fun a : U.right ⟶ σ.obj j => U.hom ≫ a)
            (Category.assoc (eqToHom κ)
              (σ.map (homOfLE (show i₀ ≤ i from Nat.zero_le i.val))) (σ.map f)).symm).trans
              (Category.assoc U.hom
                (eqToHom κ ≫ σ.map (homOfLE (show i₀ ≤ i from Nat.zero_le i.val)))
                (σ.map f)).symm) }

/-- Its literal original projected functor is the given base simplex. -/
theorem simplexLiftFromFirst_projection
    {C : Type u} [Category.{v} C] (y : C) {n : ℕ}
    (σ : ComposableArrows C n) (U : Under y) (κ : U.right = σ.left) :
    ((Under.forget y).mapComposableArrows n).obj (simplexLiftFromFirst y σ U κ) = σ := by
  rfl

/-- Its original first object is the prescribed Under object, with the
endpoint equality transported explicitly. -/
theorem simplexLiftFromFirst_first
    {C : Type u} [Category.{v} C] (y : C) {n : ℕ}
    (σ : ComposableArrows C n) (U : Under y) (κ : U.right = σ.left) :
    (simplexLiftFromFirst y σ U κ).left = U := by
  have h00 :
      (homOfLE (show (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≤
          (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) from Nat.zero_le 0) :
        (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ⟶
          (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) =
        𝟙 (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) :=
    Subsingleton.elim _ _
  refine StructuredArrow.obj_ext (simplexLiftFromFirst y σ U κ).left U κ.symm ?_
  change (U.hom ≫ eqToHom κ ≫
      σ.map (homOfLE (show (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≤
        (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) from Nat.zero_le 0))) ≫
        eqToHom κ.symm = U.hom
  rw [h00, Functor.map_id]
  simp only [Category.comp_id, Category.assoc, eqToHom_trans, eqToHom_refl]

end CategoryTheory.Under
namespace CategoryTheory.Under

/-- The original Under projection has a unique lift of each simplex from the
prescribed first object and its actual endpoint equality. -/
theorem existsUnique_simplexLiftFromFirst
    {C : Type u} [Category.{v} C] (y : C) {n : ℕ}
    (σ : ComposableArrows C n) (U : Under y) (κ : U.right = σ.left) :
    ∃! τ : ComposableArrows (Under y) n,
      ((Under.forget y).mapComposableArrows n).obj τ = σ ∧ τ.left = U := by
  let L : ComposableArrows (Under y) n := simplexLiftFromFirst y σ U κ
  refine ⟨L, ⟨simplexLiftFromFirst_projection y σ U κ,
    simplexLiftFromFirst_first y σ U κ⟩, ?_⟩
  intro τ hτ
  have H : τ ⋙ Under.forget y = σ := hτ.1
  have HL : L ⋙ Under.forget y = σ := simplexLiftFromFirst_projection y σ U κ
  let i₀ : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have h₀ : τ.obj i₀ = U := hτ.2
  let ε₀ : (τ.obj i₀).right = σ.obj i₀ := Functor.congr_obj H i₀
  let εs : U.right = (τ.obj i₀).right :=
    congrArg (fun V : Under y => V.right) h₀.symm
  have hεκ : εs.trans ε₀ = κ := Subsingleton.elim _ _
  have hsrc : eqToHom εs ≫ eqToHom ε₀ = eqToHom κ :=
    (eqToHom_trans εs ε₀).trans
      (congrArg (fun h : U.right = σ.obj i₀ => eqToHom h) hεκ)
  have hobj (j : Fin (n + 1)) : τ.obj j = L.obj j := by
    let a : i₀ ⟶ j := homOfLE (show i₀ ≤ j from Nat.zero_le j.val)
    let f : U ⟶ τ.obj j := eqToHom h₀.symm ≫ τ.map a
    let εj : (τ.obj j).right = σ.obj j := Functor.congr_obj H j
    have he : (eqToHom h₀.symm : U ⟶ τ.obj i₀).right = eqToHom εs :=
      Under.eqToHom_right h₀.symm
    have hf : f.right = eqToHom εs ≫ (τ.map a).right :=
      (Under.comp_right U (τ.obj i₀) (τ.obj j) (eqToHom h₀.symm) (τ.map a)).trans
        (congrArg (fun r : U.right ⟶ (τ.obj i₀).right => r ≫ (τ.map a).right) he)
    have hm : (τ.map a).right = eqToHom ε₀ ≫ σ.map a ≫ eqToHom εj.symm := by
      simpa only [Functor.comp_obj, Functor.comp_map, Under.forget_obj,
        Under.forget_map] using (Functor.congr_hom H a)
    have hmp : (τ.map a).right ≫ eqToHom εj = eqToHom ε₀ ≫ σ.map a := by
      have h := congrArg (fun r : (τ.obj i₀).right ⟶ (τ.obj j).right =>
        r ≫ eqToHom εj) hm
      simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h
    have hfp : f.right ≫ eqToHom εj = eqToHom κ ≫ σ.map a :=
      (congrArg (fun r : U.right ⟶ (τ.obj j).right => r ≫ eqToHom εj) hf).trans
        ((Category.assoc (eqToHom εs) (τ.map a).right (eqToHom εj)).trans
          ((congrArg (fun r : (τ.obj i₀).right ⟶ σ.obj j => eqToHom εs ≫ r) hmp).trans
            ((Category.assoc (eqToHom εs) (eqToHom ε₀) (σ.map a)).symm.trans
              (congrArg (fun r : U.right ⟶ σ.obj i₀ => r ≫ σ.map a) hsrc))))
    have hforced : τ.obj j = Under.mk (U.hom ≫ eqToHom κ ≫ σ.map a) :=
      lift_object_unique y U (eqToHom κ ≫ σ.map a) (τ.obj j) εj f hfp
    have hcanonical : L.obj j = Under.mk (U.hom ≫ eqToHom κ ≫ σ.map a) := rfl
    exact hforced.trans hcanonical.symm
  have HB : τ ⋙ Under.forget y = L ⋙ Under.forget y := H.trans HL.symm
  refine Functor.ext (F := τ) (G := L) hobj ?_
  intro i j f
  apply (Under.forget y).map_injective
  simpa only [Functor.comp_obj, Functor.comp_map, Under.forget_obj,
    Under.forget_map, Under.comp_right, Under.eqToHom_right] using
      (Functor.congr_hom HB f)

end CategoryTheory.Under
namespace CategoryTheory.Under

/-- Reindexing the original lift is the canonical lift of the reindexed
simplex from its actual changed first object. -/
theorem simplexLiftFromFirst_reindex
    {C : Type u} [Category.{v} C] (y : C) {m n : ℕ}
    (σ : ComposableArrows C n) (U : Under y) (κ : U.right = σ.left)
    (α : Fin (m + 1) ⥤ Fin (n + 1)) :
    α ⋙ simplexLiftFromFirst y σ U κ =
      simplexLiftFromFirst y (α ⋙ σ)
        (ComposableArrows.left (C := Under y) (n := m)
          (α ⋙ simplexLiftFromFirst y σ U κ))
        (by rfl) := by
  let L : ComposableArrows (Under y) n := simplexLiftFromFirst y σ U κ
  let Uα : Under y := ComposableArrows.left (C := Under y) (n := m) (α ⋙ L)
  have κα : Uα.right = ComposableArrows.left (C := C) (n := m) (α ⋙ σ) := rfl
  let R : ComposableArrows (Under y) m := simplexLiftFromFirst y (α ⋙ σ) Uα κα
  have HL : L ⋙ Under.forget y = σ := simplexLiftFromFirst_projection y σ U κ
  have HA : ((Under.forget y).mapComposableArrows m).obj (α ⋙ L) = α ⋙ σ :=
    congrArg (fun F : ComposableArrows C n => α ⋙ F) HL
  have HR : ((Under.forget y).mapComposableArrows m).obj R = α ⋙ σ :=
    simplexLiftFromFirst_projection y (α ⋙ σ) Uα κα
  have HRA : R.left = Uα := simplexLiftFromFirst_first y (α ⋙ σ) Uα κα
  obtain ⟨W, _, hUnique⟩ := existsUnique_simplexLiftFromFirst y (α ⋙ σ) Uα κα
  exact (hUnique (α ⋙ L) ⟨HA, rfl⟩).trans (hUnique R ⟨HR, HRA⟩).symm

end CategoryTheory.Under
namespace SSet.KanComplex

/-- The original cover vertex determines the actual first object of the base nerve chain. -/
theorem nativeCoverSimplex_firstAnchor_eq
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (v : (nativeCover X x) _⦋0⦌)
    (hv : (SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ =
      (SSet.const ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v) :
        (Δ[0] : SSet.{u}) ⟶ X)) :
    (CategoryTheory.nerveEquiv (C := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
      ((nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌) v)).right =
      ComposableArrows.left (C := SSet.FundamentalGroupoid X) (n := n)
        (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X)) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let P : SSet.{u} := nativeCover X x
  let Y : SSet.{u} := CategoryTheory.nerve Γ
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let q : A ⟶ Y := nativeCoverNerveProjection X x
  let z : X _⦋0⦌ := p.app (Opposite.op ⦋0⦌) v
  let a : A _⦋0⦌ := r.app (Opposite.op ⦋0⦌) v
  let U : CategoryTheory.Under y := CategoryTheory.nerveEquiv a
  let t : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ η)
  let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ k
  let v0 : (Δ[n] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm k
  have hrepr : SSet.stdSimplex.objEquiv.symm θ = v0 := rfl
  have hm : (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)) (SSet.stdSimplex.map θ) = v0 :=
    (SSet.yonedaEquiv_map θ).trans hrepr
  have hi : (SSet.stdSimplex.map θ : (Δ[0] : SSet.{u}) ⟶ Δ[n]) =
      SSet.yonedaEquiv.symm v0 :=
    (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)).eq_symm_apply.mpr hm
  have hb : (SSet.yonedaEquiv.symm v0 : (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ =
      (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) := hv
  have h0 : SSet.stdSimplex.map θ ≫ σ =
      (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) :=
    (congrArg (fun i : (Δ[0] : SSet.{u}) ⟶ Δ[n] => i ≫ σ) hi).trans hb
  have hφ : SSet.stdSimplex.map θ ≫ (σ ≫ η) =
      (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ η :=
    (Category.assoc (SSet.stdSimplex.map θ) σ η).symm.trans
      (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ X => f ≫ η) h0)
  have hy1 : Y.map θ.op t =
      (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌)) (SSet.stdSimplex.map θ ≫ (σ ≫ η)) :=
    SSet.yonedaEquiv_naturality θ (σ ≫ η)
  have hy2 : (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌))
      (SSet.stdSimplex.map θ ≫ (σ ≫ η)) =
      (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌))
        ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ η) :=
    congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ Y =>
      (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌)) f) hφ
  have hy3 : (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌))
      ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ η) =
      η.app (Opposite.op ⦋0⦌) z :=
    (SSet.yonedaEquiv_comp (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) η).trans
      (congrArg (fun w : X _⦋0⦌ => η.app (Opposite.op ⦋0⦌) w)
        (SSet.yonedaEquiv_const z))
  have hy : Y.map θ.op t = η.app (Opposite.op ⦋0⦌) z := (hy1.trans hy2).trans hy3
  have hc : p ≫ η = r ≫ q := nativeCoverProjection_condition
  have hs : η.app (Opposite.op ⦋0⦌) z = q.app (Opposite.op ⦋0⦌) a := by
    change (p ≫ η).app (Opposite.op ⦋0⦌) v = (r ≫ q).app (Opposite.op ⦋0⦌) v
    exact congrArg (fun f : P ⟶ Y => f.app (Opposite.op ⦋0⦌) v) hc
  have hleft : (CategoryTheory.nerveEquiv (C := Γ)) (Y.map θ.op t) =
      ComposableArrows.left (C := Γ) (n := n) t := rfl
  have ha : (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm U = a :=
    (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm_apply_apply a
  have hqU : q.app (Opposite.op ⦋0⦌)
      ((CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm U) =
      (CategoryTheory.nerveEquiv (C := Γ)).symm U.right := by
    dsimp only [q, nativeCoverNerveProjection]
    exact CategoryTheory.nerveMap_app_mk₀ (CategoryTheory.Under.forget y) U
  have hqa : q.app (Opposite.op ⦋0⦌) a =
      (CategoryTheory.nerveEquiv (C := Γ)).symm U.right :=
    (congrArg (fun w : A _⦋0⦌ => q.app (Opposite.op ⦋0⦌) w) ha).symm.trans hqU
  have hr : (CategoryTheory.nerveEquiv (C := Γ)) (q.app (Opposite.op ⦋0⦌) a) =
      U.right :=
    (congrArg (fun w : Y _⦋0⦌ => (CategoryTheory.nerveEquiv (C := Γ)) w) hqa).trans
      ((CategoryTheory.nerveEquiv (C := Γ)).apply_symm_apply U.right)
  have ht : ComposableArrows.left (C := Γ) (n := n) t = U.right :=
    hleft.symm.trans
      ((congrArg (fun w : Y _⦋0⦌ => (CategoryTheory.nerveEquiv (C := Γ)) w)
        (hy.trans hs)).trans hr)
  exact ht.symm

end SSet.KanComplex
namespace SSet.KanComplex

section

variable {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
variable (σ : (Δ[n] : SSet.{u}) ⟶ X) (v : (nativeCover X x) _⦋0⦌)
variable (hv : (SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
      (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ =
  (SSet.const ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v) :
    (Δ[0] : SSet.{u}) ⟶ X))

/-- The canonical Under simplex supplies the actual original pullback square. -/
private theorem nativeCoverFirstSimplex_square :
    σ ≫ nativeCoverUnit X =
      (SSet.yonedaEquiv
        (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
        (n := ⦋n⦌)).symm
          (CategoryTheory.Under.simplexLiftFromFirst (SSet.FundamentalGroupoid.mk x)
            (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X))
            (CategoryTheory.nerveEquiv
              (C := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
              ((nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌) v))
            (by exact nativeCoverSimplex_firstAnchor_eq σ v hv)) ≫
        nativeCoverNerveProjection X x := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let Y : SSet.{u} := CategoryTheory.nerve Γ
  let η : X ⟶ Y := nativeCoverUnit X
  let q : A ⟶ Y := nativeCoverNerveProjection X x
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ η)
  let U : CategoryTheory.Under y := CategoryTheory.nerveEquiv
    ((nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌) v)
  have κ : U.right = ComposableArrows.left (C := Γ) (n := n) T :=
    nativeCoverSimplex_firstAnchor_eq σ v hv
  let τ : ComposableArrows (CategoryTheory.Under y) n :=
    CategoryTheory.Under.simplexLiftFromFirst y T U κ
  let φ : (Δ[n] : SSet.{u}) ⟶ A :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).symm τ
  have hp : q.app (Opposite.op ⦋n⦌) τ = T := by
    dsimp only [q, nativeCoverNerveProjection]
    exact CategoryTheory.Under.simplexLiftFromFirst_projection y T U κ
  have ht : (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)) φ = τ :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).apply_symm_apply τ
  have hφ : (SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)) (φ ≫ q) = T :=
    (SSet.yonedaEquiv_comp φ q).trans
      ((congrArg (fun a : A _⦋n⦌ => q.app (Opposite.op ⦋n⦌) a) ht).trans hp)
  have hs : (SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)) (σ ≫ η) = T := rfl
  have he : σ ≫ η = φ ≫ q :=
    (SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)).injective (hs.trans hφ.symm)
  exact he

/-- Lift the actual base simplex from its original first cover vertex. -/
noncomputable def nativeCoverSimplexLiftFromFirstMap :
    (Δ[n] : SSet.{u}) ⟶ nativeCover X x :=
  pullback.lift σ
    ((SSet.yonedaEquiv
      (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
      (n := ⦋n⦌)).symm
        (CategoryTheory.Under.simplexLiftFromFirst (SSet.FundamentalGroupoid.mk x)
          (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X))
          (CategoryTheory.nerveEquiv
            (C := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
            ((nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌) v))
          (by exact nativeCoverSimplex_firstAnchor_eq σ v hv)))
    (by exact nativeCoverFirstSimplex_square σ v hv)

/-- The actual first projection is the original base simplex. -/
theorem nativeCoverSimplexLiftFromFirstMap_projection :
    nativeCoverSimplexLiftFromFirstMap σ v hv ≫ nativeCoverProjection X x = σ := by
  dsimp only [nativeCoverSimplexLiftFromFirstMap, nativeCoverProjection]
  exact pullback.lift_fst _ _ _

/-- The actual second projection is the canonical Under chain with the derived first anchor. -/
theorem nativeCoverSimplexLiftFromFirstMap_underProjection :
    nativeCoverSimplexLiftFromFirstMap σ v hv ≫ nativeCoverUnderProjection X x =
      (SSet.yonedaEquiv
        (X := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)))
        (n := ⦋n⦌)).symm
          (CategoryTheory.Under.simplexLiftFromFirst (SSet.FundamentalGroupoid.mk x)
            (SSet.yonedaEquiv (σ ≫ nativeCoverUnit X))
            (CategoryTheory.nerveEquiv
              (C := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
              ((nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌) v))
            (by exact nativeCoverSimplex_firstAnchor_eq σ v hv)) := by
  dsimp only [nativeCoverSimplexLiftFromFirstMap, nativeCoverUnderProjection]
  exact pullback.lift_snd _ _ _

/-- The lifted simplex has exactly the original first cover vertex. -/
theorem nativeCoverSimplexLiftFromFirstMap_firstVertex :
    (SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
        (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ nativeCoverSimplexLiftFromFirstMap σ v hv =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ nativeCover X x) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let Y : SSet.{u} := CategoryTheory.nerve Γ
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ η)
  let U : CategoryTheory.Under y := CategoryTheory.nerveEquiv
    (r.app (Opposite.op ⦋0⦌) v)
  have κ : U.right = ComposableArrows.left (C := Γ) (n := n) T :=
    nativeCoverSimplex_firstAnchor_eq σ v hv
  let τ : ComposableArrows (CategoryTheory.Under y) n :=
    CategoryTheory.Under.simplexLiftFromFirst y T U κ
  let φ : (Δ[n] : SSet.{u}) ⟶ A :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).symm τ
  let L : (Δ[n] : SSet.{u}) ⟶ P := nativeCoverSimplexLiftFromFirstMap σ v hv
  let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ k
  let v0 : (Δ[n] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm k
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm v0
  have hLp : L ≫ p = σ := nativeCoverSimplexLiftFromFirstMap_projection σ v hv
  have hLr : L ≫ r = φ := nativeCoverSimplexLiftFromFirstMap_underProjection σ v hv
  have hpv : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) ≫ p =
      (SSet.const (p.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ X) :=
    SSet.const_comp v p
  have hxp : (i ≫ L) ≫ p =
      (SSet.const (p.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ X) :=
    (Category.assoc i L p).trans
      ((congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => i ≫ f) hLp).trans hv)
  have hpfield : (i ≫ L) ≫ p = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) ≫ p :=
    hxp.trans hpv.symm
  have hrepr : SSet.stdSimplex.objEquiv.symm θ = v0 := rfl
  have hm : (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)) (SSet.stdSimplex.map θ) = v0 :=
    (SSet.yonedaEquiv_map θ).trans hrepr
  have hi : (SSet.stdSimplex.map θ : (Δ[0] : SSet.{u}) ⟶ Δ[n]) = i :=
    (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)).eq_symm_apply.mpr hm
  have ht : (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)) φ = τ :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).apply_symm_apply τ
  have hy1 : (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (i ≫ φ) =
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (SSet.stdSimplex.map θ ≫ φ) :=
    congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ A =>
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) f)
        (congrArg (fun j : (Δ[0] : SSet.{u}) ⟶ Δ[n] => j ≫ φ) hi.symm)
  have hy2 : (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (SSet.stdSimplex.map θ ≫ φ) =
      A.map θ.op ((SSet.yonedaEquiv (X := A) (n := ⦋n⦌)) φ) :=
    (SSet.yonedaEquiv_naturality θ φ).symm
  have hy3 : A.map θ.op ((SSet.yonedaEquiv (X := A) (n := ⦋n⦌)) φ) = A.map θ.op τ :=
    congrArg (fun a : A _⦋n⦌ => A.map θ.op a) ht
  have hf : (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)) (A.map θ.op τ) =
      ComposableArrows.left (C := CategoryTheory.Under y) (n := n) τ := rfl
  have hτ0 : ComposableArrows.left (C := CategoryTheory.Under y) (n := n) τ = U :=
    CategoryTheory.Under.simplexLiftFromFirst_first y T U κ
  have hobj : (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)) (A.map θ.op τ) =
      (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
        (r.app (Opposite.op ⦋0⦌) v) := hf.trans hτ0
  have hfirst : A.map θ.op τ = r.app (Opposite.op ⦋0⦌) v :=
    (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).injective hobj
  have hφv : (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (i ≫ φ) =
      r.app (Opposite.op ⦋0⦌) v := ((hy1.trans hy2).trans hy3).trans hfirst
  have hc : (SSet.yonedaEquiv (X := A) (n := ⦋0⦌))
      (SSet.const (r.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ A) =
      r.app (Opposite.op ⦋0⦌) v := SSet.yonedaEquiv_const _
  have hφ0 : i ≫ φ =
      (SSet.const (r.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ A) :=
    (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)).injective (hφv.trans hc.symm)
  have hrv : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) ≫ r =
      (SSet.const (r.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ A) :=
    SSet.const_comp v r
  have hxr : (i ≫ L) ≫ r =
      (SSet.const (r.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ A) :=
    (Category.assoc i L r).trans
      ((congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ A => i ≫ f) hLr).trans hφ0)
  have hrfield : (i ≫ L) ≫ r = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) ≫ r :=
    hxr.trans hrv.symm
  exact nativeCover_hom_ext hpfield hrfield

end

end SSet.KanComplex
namespace SSet.KanComplex

/-- A base simplex and its original first cover vertex have a unique actual cover lift. -/
theorem existsUnique_nativeCoverSimplexLiftFromFirst
    {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (v : (nativeCover X x) _⦋0⦌)
    (hv : (SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ =
      (SSet.const ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v) :
        (Δ[0] : SSet.{u}) ⟶ X)) :
    ∃! a : (Δ[n] : SSet.{u}) ⟶ nativeCover X x,
      a ≫ nativeCoverProjection X x = σ ∧
        (SSet.yonedaEquiv.symm
          (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
            (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ a =
          (SSet.const v : (Δ[0] : SSet.{u}) ⟶ nativeCover X x) := by
  refine ⟨nativeCoverSimplexLiftFromFirstMap σ v hv,
    ⟨nativeCoverSimplexLiftFromFirstMap_projection σ v hv,
      nativeCoverSimplexLiftFromFirstMap_firstVertex σ v hv⟩, ?_⟩
  intro a ha
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let P : SSet.{u} := nativeCover X x
  let Y : SSet.{u} := CategoryTheory.nerve Γ
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let q : A ⟶ Y := nativeCoverNerveProjection X x
  let T : ComposableArrows Γ n := SSet.yonedaEquiv (σ ≫ η)
  let U : CategoryTheory.Under y := CategoryTheory.nerveEquiv
    (r.app (Opposite.op ⦋0⦌) v)
  have κ : U.right = ComposableArrows.left (C := Γ) (n := n) T :=
    nativeCoverSimplex_firstAnchor_eq σ v hv
  let τ : ComposableArrows (CategoryTheory.Under y) n :=
    CategoryTheory.Under.simplexLiftFromFirst y T U κ
  let φ : (Δ[n] : SSet.{u}) ⟶ A :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).symm τ
  let L : (Δ[n] : SSet.{u}) ⟶ P := nativeCoverSimplexLiftFromFirstMap σ v hv
  let R : ComposableArrows (CategoryTheory.Under y) n := SSet.yonedaEquiv (a ≫ r)
  let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ k
  let v0 : (Δ[n] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm k
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm v0
  have hap : a ≫ p = σ := ha.1
  have hai : i ≫ a = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) := ha.2
  have hc : p ≫ η = r ≫ q := nativeCoverProjection_condition
  have hbase : (a ≫ r) ≫ q = σ ≫ η :=
    (Category.assoc a r q).trans
      ((congrArg (fun f : P ⟶ Y => a ≫ f) hc.symm).trans
        ((Category.assoc a p η).symm.trans
          (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => f ≫ η) hap)))
  have hY : (SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)) ((a ≫ r) ≫ q) = T :=
    congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ Y =>
      (SSet.yonedaEquiv (X := Y) (n := ⦋n⦌)) f) hbase
  have hqR : q.app (Opposite.op ⦋n⦌) R = T :=
    (SSet.yonedaEquiv_comp (a ≫ r) q).symm.trans hY
  have hR : ((CategoryTheory.Under.forget y).mapComposableArrows n).obj R = T := by
    dsimp only [q, nativeCoverNerveProjection] at hqR
    exact hqR
  have hrepr : SSet.stdSimplex.objEquiv.symm θ = v0 := rfl
  have hm : (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)) (SSet.stdSimplex.map θ) = v0 :=
    (SSet.yonedaEquiv_map θ).trans hrepr
  have hi : (SSet.stdSimplex.map θ : (Δ[0] : SSet.{u}) ⟶ Δ[n]) = i :=
    (SSet.yonedaEquiv (X := Δ[n]) (n := ⦋0⦌)).eq_symm_apply.mpr hm
  have hfirst : i ≫ (a ≫ r) =
      (SSet.const (r.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ A) :=
    (Category.assoc i a r).symm.trans
      ((congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ P => f ≫ r) hai).trans
        (SSet.const_comp v r))
  have hy1 : A.map θ.op R =
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (SSet.stdSimplex.map θ ≫ (a ≫ r)) :=
    SSet.yonedaEquiv_naturality θ (a ≫ r)
  have hy2 : (SSet.yonedaEquiv (X := A) (n := ⦋0⦌))
      (SSet.stdSimplex.map θ ≫ (a ≫ r)) =
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (i ≫ (a ≫ r)) :=
    congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ A =>
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) f)
        (congrArg (fun j : (Δ[0] : SSet.{u}) ⟶ Δ[n] => j ≫ (a ≫ r)) hi)
  have hy3 : (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) (i ≫ (a ≫ r)) =
      r.app (Opposite.op ⦋0⦌) v :=
    (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ A =>
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) f) hfirst).trans
        (SSet.yonedaEquiv_const _)
  have hvertex : A.map θ.op R = r.app (Opposite.op ⦋0⦌) v :=
    (hy1.trans hy2).trans hy3
  have hleft : (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
      (A.map θ.op R) =
      ComposableArrows.left (C := CategoryTheory.Under y) (n := n) R := rfl
  have hRU : ComposableArrows.left (C := CategoryTheory.Under y) (n := n) R = U :=
    hleft.symm.trans
      (congrArg (fun w : A _⦋0⦌ =>
        (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)) w) hvertex)
  obtain ⟨W, _, hUnique⟩ :=
    CategoryTheory.Under.existsUnique_simplexLiftFromFirst y T U κ
  have hτp : ((CategoryTheory.Under.forget y).mapComposableArrows n).obj τ = T :=
    CategoryTheory.Under.simplexLiftFromFirst_projection y T U κ
  have hτ0 : ComposableArrows.left (C := CategoryTheory.Under y) (n := n) τ = U :=
    CategoryTheory.Under.simplexLiftFromFirst_first y T U κ
  have hRτ : R = τ :=
    (hUnique R ⟨hR, hRU⟩).trans (hUnique τ ⟨hτp, hτ0⟩).symm
  have hφ : (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)) φ = τ :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).apply_symm_apply τ
  have har : a ≫ r = φ :=
    (SSet.yonedaEquiv (X := A) (n := ⦋n⦌)).injective (hRτ.trans hφ.symm)
  have hLp : L ≫ p = σ := nativeCoverSimplexLiftFromFirstMap_projection σ v hv
  have hLr : L ≫ r = φ := nativeCoverSimplexLiftFromFirstMap_underProjection σ v hv
  have hpfield : a ≫ p = L ≫ p := hap.trans hLp.symm
  have hrfield : a ≫ r = L ≫ r := har.trans hLr.symm
  exact nativeCover_hom_ext hpfield hrfield

end SSet.KanComplex
namespace SSet.KanComplex

/-- Every simplex map into the literal native cover fiber is constant at its actual first vertex. -/
theorem nativeCover_fiber_simplexMap_eq_const
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶
      (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u})) :
    a = SSet.const
      ((SSet.yonedaEquiv
        (X := (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}))
        (n := ⦋0⦌))
          ((SSet.yonedaEquiv.symm
            (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
              (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ a)) := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let F : SSet.Subcomplex P := SSet.Subcomplex.fiber p z
  let e : (F : SSet.{u}) ⟶ P := F.ι
  let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let v0 : (Δ[n] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm k
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm v0
  let vF : (F : SSet.{u}) _⦋0⦌ :=
    (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌)) (i ≫ a)
  let v : P _⦋0⦌ := e.app (Opposite.op ⦋0⦌) vF
  have hv : p.app (Opposite.op ⦋0⦌) v = z :=
    (SSet.Subcomplex.mem_fiber_obj_zero_iff p z).mp vF.property
  have hep : e ≫ p = (SSet.const z : (F : SSet.{u}) ⟶ X) :=
    SSet.Subcomplex.fiber_ι_comp p z
  have hpa : (a ≫ e) ≫ p = (SSet.const z : (Δ[n] : SSet.{u}) ⟶ X) :=
    (Category.assoc a e p).trans
      ((congrArg (fun f : (F : SSet.{u}) ⟶ X => a ≫ f) hep).trans
        (SSet.comp_const a z))
  have hvi : (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌)) (i ≫ a) = vF := rfl
  have hci : (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌))
      (SSet.const vF : (Δ[0] : SSet.{u}) ⟶ (F : SSet.{u})) = vF :=
    SSet.yonedaEquiv_const vF
  have hai : i ≫ a = (SSet.const vF : (Δ[0] : SSet.{u}) ⟶ (F : SSet.{u})) :=
    (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌)).injective (hvi.trans hci.symm)
  have hfirst : i ≫ (a ≫ e) = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) :=
    (Category.assoc i a e).symm.trans
      ((congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ (F : SSet.{u}) => f ≫ e) hai).trans
        (SSet.const_comp vF e))
  have hcompat : i ≫ (SSet.const z : (Δ[n] : SSet.{u}) ⟶ X) =
      (SSet.const (p.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ X) :=
    (SSet.comp_const i z).trans
      (congrArg (fun w : X _⦋0⦌ => (SSet.const w : (Δ[0] : SSet.{u}) ⟶ X)) hv.symm)
  obtain ⟨W, _, hUnique⟩ :=
    existsUnique_nativeCoverSimplexLiftFromFirst
      (SSet.const z : (Δ[n] : SSet.{u}) ⟶ X) v hcompat
  have hpc : (SSet.const v : (Δ[n] : SSet.{u}) ⟶ P) ≫ p =
      (SSet.const z : (Δ[n] : SSet.{u}) ⟶ X) :=
    (SSet.const_comp v p).trans
      (congrArg (fun w : X _⦋0⦌ => (SSet.const w : (Δ[n] : SSet.{u}) ⟶ X)) hv)
  have hfc : i ≫ (SSet.const v : (Δ[n] : SSet.{u}) ⟶ P) =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) := SSet.comp_const i v
  have hP : a ≫ e = (SSet.const v : (Δ[n] : SSet.{u}) ⟶ P) :=
    (hUnique (a ≫ e) ⟨hpa, hfirst⟩).trans
      (hUnique (SSet.const v : (Δ[n] : SSet.{u}) ⟶ P) ⟨hpc, hfc⟩).symm
  have hec : (SSet.const vF : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u})) ≫ e =
      (SSet.const v : (Δ[n] : SSet.{u}) ⟶ P) := SSet.const_comp vF e
  have heq : a ≫ e = (SSet.const vF : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u})) ≫ e :=
    hP.trans hec.symm
  exact (cancel_mono e).mp heq

end SSet.KanComplex
namespace SSet.KanComplex

/-- The literal vertices over z are equivalent to the actual n-simplices of its strict fiber. -/
noncomputable def nativeCoverFiberSimplexEquiv
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) (n : ℕ) :
    {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z} ≃
      (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌ := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let F : SSet.Subcomplex P := SSet.Subcomplex.fiber p z
  let V : Type u := {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z}
  let vertexEquiv : V ≃ (F : SSet.{u}) _⦋0⦌ :=
    { toFun := fun v => ⟨v.val, (SSet.Subcomplex.mem_fiber_obj_zero_iff p z).mpr v.property⟩
      invFun := fun v => ⟨v.val, (SSet.Subcomplex.mem_fiber_obj_zero_iff p z).mp v.property⟩
      left_inv := fun v => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }
  let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let v0 : (Δ[n] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm k
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm v0
  let simplexEquiv : (F : SSet.{u}) _⦋0⦌ ≃ (F : SSet.{u}) _⦋n⦌ :=
    { toFun := fun v => (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌))
        (SSet.const v : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u}))
      invFun := fun s => (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌))
        (i ≫ (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)).symm s)
      left_inv := by
        intro v
        let c : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u}) := SSet.const v
        have hc : (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)).symm
            ((SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)) c) = c :=
          (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)).symm_apply_apply c
        have h1 : i ≫ (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)).symm
            ((SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)) c) = i ≫ c :=
          congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u}) => i ≫ f) hc
        have h2 : i ≫ c = (SSet.const v : (Δ[0] : SSet.{u}) ⟶ (F : SSet.{u})) :=
          SSet.comp_const i v
        have h3 : (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌))
            (SSet.const v : (Δ[0] : SSet.{u}) ⟶ (F : SSet.{u})) = v :=
          SSet.yonedaEquiv_const v
        exact (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ (F : SSet.{u}) =>
          (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌)) f) (h1.trans h2)).trans h3
      right_inv := by
        intro s
        let a : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u}) :=
          (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)).symm s
        let v : (F : SSet.{u}) _⦋0⦌ :=
          (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋0⦌)) (i ≫ a)
        have hc : a = (SSet.const v : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u})) :=
          nativeCover_fiber_simplexMap_eq_const z a
        have h1 : (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)) a =
            (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌))
              (SSet.const v : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u})) :=
          congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ (F : SSet.{u}) =>
            (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)) f) hc
        have h2 : (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)) a = s :=
          (SSet.yonedaEquiv (X := (F : SSet.{u})) (n := ⦋n⦌)).apply_symm_apply s
        exact h1.symm.trans h2 }
  exact vertexEquiv.trans simplexEquiv

/-- The forward component is the actual degenerate constant simplex of the subtype vertex. -/
theorem nativeCoverFiberSimplexEquiv_apply
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) (n : ℕ)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    nativeCoverFiberSimplexEquiv z n v =
      (SSet.yonedaEquiv
        (X := (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}))
        (n := ⦋n⦌))
          (SSet.const
            (⟨v.val, (SSet.Subcomplex.mem_fiber_obj_zero_iff
              (nativeCoverProjection X x) z).mpr v.property⟩ :
                (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋0⦌) :
            (Δ[n] : SSet.{u}) ⟶
              (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u})) := by
  dsimp only [nativeCoverFiberSimplexEquiv]
  rfl

/-- The inverse component's original P vertex is the actual first-vertex restriction. -/
theorem nativeCoverFiberSimplexEquiv_symm_val
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) (n : ℕ)
    (s : (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) :
    ((nativeCoverFiberSimplexEquiv z n).symm s).val =
      ((SSet.yonedaEquiv
        (X := (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}))
        (n := ⦋0⦌))
          ((SSet.yonedaEquiv.symm
            (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
              (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫
            (SSet.yonedaEquiv
              (X := (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}))
              (n := ⦋n⦌)).symm s)).val := by
  dsimp only [nativeCoverFiberSimplexEquiv]
  rfl

end SSet.KanComplex
namespace SSet.KanComplex

/-- The literal strict fiber is naturally the constant simplicial set on its actual vertices. -/
noncomputable def nativeCoverFiberConstIso
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) :
    ((Functor.const SimplexCategoryᵒᵖ).obj
      {v : (nativeCover X x) _⦋0⦌ //
        (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) ≅
      (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) := by
  let V : Type u := {v : (nativeCover X x) _⦋0⦌ //
    (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  let F : SSet.{u} :=
    (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u})
  let K : SSet.{u} := (Functor.const SimplexCategoryᵒᵖ).obj V
  let app : ∀ d : SimplexCategoryᵒᵖ, K.obj d ≅ F.obj d := fun d =>
    (nativeCoverFiberSimplexEquiv (X := X) (x := x) z d.unop.len).toIso
  have hmap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (v : V) :
      F.map θ.op (nativeCoverFiberSimplexEquiv (X := X) (x := x) z n v) =
        nativeCoverFiberSimplexEquiv (X := X) (x := x) z m v := by
    let vF : F _⦋0⦌ :=
      ⟨v.val, (SSet.Subcomplex.mem_fiber_obj_zero_iff
        (nativeCoverProjection X x) z).mpr v.property⟩
    let c : (Δ[n] : SSet.{u}) ⟶ F := SSet.const vF
    have hcn : nativeCoverFiberSimplexEquiv (X := X) (x := x) z n v =
        (SSet.yonedaEquiv (X := F) (n := ⦋n⦌)) c :=
      nativeCoverFiberSimplexEquiv_apply z n v
    have hcm : nativeCoverFiberSimplexEquiv (X := X) (x := x) z m v =
        (SSet.yonedaEquiv (X := F) (n := ⦋m⦌))
          (SSet.const vF : (Δ[m] : SSet.{u}) ⟶ F) :=
      nativeCoverFiberSimplexEquiv_apply z m v
    have hn : F.map θ.op ((SSet.yonedaEquiv (X := F) (n := ⦋n⦌)) c) =
        (SSet.yonedaEquiv (X := F) (n := ⦋m⦌)) (SSet.stdSimplex.map θ ≫ c) :=
      SSet.yonedaEquiv_naturality θ c
    have hc : SSet.stdSimplex.map θ ≫ c =
        (SSet.const vF : (Δ[m] : SSet.{u}) ⟶ F) :=
      SSet.comp_const (SSet.stdSimplex.map θ) vF
    have h1 : F.map θ.op (nativeCoverFiberSimplexEquiv (X := X) (x := x) z n v) =
        F.map θ.op ((SSet.yonedaEquiv (X := F) (n := ⦋n⦌)) c) :=
      congrArg (fun s : F _⦋n⦌ => F.map θ.op s) hcn
    have h2 : (SSet.yonedaEquiv (X := F) (n := ⦋m⦌))
          (SSet.stdSimplex.map θ ≫ c) =
        (SSet.yonedaEquiv (X := F) (n := ⦋m⦌))
          (SSet.const vF : (Δ[m] : SSet.{u}) ⟶ F) :=
      congrArg (fun f : (Δ[m] : SSet.{u}) ⟶ F =>
        (SSet.yonedaEquiv (X := F) (n := ⦋m⦌)) f) hc
    exact h1.trans (hn.trans (h2.trans hcm.symm))
  refine NatIso.ofComponents (F := K) (G := F) app ?_
  intro d e α
  refine ConcreteCategory.hom_ext _ _ ?_
  intro v
  change nativeCoverFiberSimplexEquiv (X := X) (x := x) z e.unop.len v =
    F.map α (nativeCoverFiberSimplexEquiv (X := X) (x := x) z d.unop.len v)
  exact (hmap (m := e.unop.len) (n := d.unop.len) α.unop v).symm

/-- The forward component is exactly the verified constant-simplex equivalence. -/
theorem nativeCoverFiberConstIso_hom_app
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) (n : ℕ)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    (nativeCoverFiberConstIso z).hom.app (Opposite.op ⦋n⦌) v =
      nativeCoverFiberSimplexEquiv z n v := by
  dsimp only [nativeCoverFiberConstIso, NatIso.ofComponents, Equiv.toIso]
  rfl

end SSet.KanComplex

public section

noncomputable section


namespace SSet.KanComplex

/-- Original cover vertices over z are the strict Under-object fiber over its native base object. -/
noncomputable def nativeCoverVertexUnderEquiv
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) :
    {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z} ≃
      {U : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) //
        U.right = SSet.FundamentalGroupoid.mk z} := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let w : Γ := SSet.FundamentalGroupoid.mk z
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let Y : SSet.{u} := CategoryTheory.nerve Γ
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let η : X ⟶ Y := nativeCoverUnit X
  let q : A ⟶ Y := nativeCoverNerveProjection X x
  let V : Type u := {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z}
  let W : Type u := {U : CategoryTheory.Under y // U.right = w}
  have hηz : η.app (Opposite.op ⦋0⦌) z =
      (CategoryTheory.nerveEquiv (C := Γ)).symm w := by
    dsimp only [η, nativeCoverUnit]
    exact SSet.fundamentalGroupoidNerveEquiv_app_zero X Γ (𝟭 Γ) z
  let toUnder : V → W := fun v => by
    let U : CategoryTheory.Under y :=
      (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
        (r.app (Opposite.op ⦋0⦌) v.val)
    let i : (Δ[0] : SSet.{u}) ⟶ Δ[0] :=
      SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ 0⟩ : Fin (0 + 1)))
    have hfirst : i ≫ (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) =
        (SSet.const (p.app (Opposite.op ⦋0⦌) v.val) : (Δ[0] : SSet.{u}) ⟶ X) :=
      (SSet.comp_const i z).trans
        (congrArg (fun t : X _⦋0⦌ => (SSet.const t : (Δ[0] : SSet.{u}) ⟶ X))
          v.property.symm)
    let t : Y _⦋0⦌ :=
      (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌))
        ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ η)
    have hright : U.right = ComposableArrows.left (C := Γ) (n := 0) t :=
      nativeCoverSimplex_firstAnchor_eq (X := X) (x := x) (n := 0)
        (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) v.val hfirst
    have ht : t = η.app (Opposite.op ⦋0⦌) z :=
      (SSet.yonedaEquiv_comp (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) η).trans
        (congrArg (fun t : X _⦋0⦌ => η.app (Opposite.op ⦋0⦌) t)
          (SSet.yonedaEquiv_const z))
    have hleft : ComposableArrows.left (C := Γ) (n := 0) t =
        (CategoryTheory.nerveEquiv (C := Γ)) t := rfl
    have hobj : (CategoryTheory.nerveEquiv (C := Γ)) t = w :=
      (congrArg (CategoryTheory.nerveEquiv (C := Γ)) (ht.trans hηz)).trans
        ((CategoryTheory.nerveEquiv (C := Γ)).apply_symm_apply w)
    exact ⟨U, hright.trans (hleft.trans hobj)⟩
  let fromUnder : ∀ U : W,
      {v : V // r.app (Opposite.op ⦋0⦌) v.val =
        (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm U.val} := fun U => by
    let zU : A _⦋0⦌ :=
      (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm U.val
    have hqU : q.app (Opposite.op ⦋0⦌) zU =
        (CategoryTheory.nerveEquiv (C := Γ)).symm U.val.right := by
      dsimp only [q, zU, nativeCoverNerveProjection]
      exact CategoryTheory.nerveMap_app_mk₀ (CategoryTheory.Under.forget y) U.val
    have hv : η.app (Opposite.op ⦋0⦌) z = q.app (Opposite.op ⦋0⦌) zU :=
      hηz.trans
        ((congrArg (CategoryTheory.nerveEquiv (C := Γ)).symm U.property.symm).trans hqU.symm)
    let a : (Δ[0] : SSet.{u}) ⟶ X :=
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm z
    let b : (Δ[0] : SSet.{u}) ⟶ A :=
      (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)).symm zU
    have ha : a ≫ η = (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌)).symm
        (η.app (Opposite.op ⦋0⦌) z) :=
      SSet.yonedaEquiv_symm_comp (X := X) (Y := Y) (n := ⦋0⦌) z η
    have hb : b ≫ q = (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌)).symm
        (q.app (Opposite.op ⦋0⦌) zU) :=
      SSet.yonedaEquiv_symm_comp (X := A) (Y := Y) (n := ⦋0⦌) zU q
    have hs : a ≫ η = b ≫ q :=
      ha.trans
        ((congrArg (SSet.yonedaEquiv (X := Y) (n := ⦋0⦌)).symm hv).trans hb.symm)
    let L : (Δ[0] : SSet.{u}) ⟶ P := pullback.lift a b hs
    let v : P _⦋0⦌ := (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)) L
    have hp : L ≫ p = a := by
      dsimp only [L, p, nativeCoverProjection]
      exact pullback.lift_fst _ _ _
    have hr : L ≫ r = b := by
      dsimp only [L, r, nativeCoverUnderProjection]
      exact pullback.lift_snd _ _ _
    have hp0 : p.app (Opposite.op ⦋0⦌) v = z :=
      (SSet.yonedaEquiv_comp L p).symm.trans
        ((congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) hp).trans
          ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).apply_symm_apply z))
    have hr0 : r.app (Opposite.op ⦋0⦌) v = zU :=
      (SSet.yonedaEquiv_comp L r).symm.trans
        ((congrArg (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) hr).trans
          ((SSet.yonedaEquiv (X := A) (n := ⦋0⦌)).apply_symm_apply zU))
    exact ⟨⟨v, hp0⟩, hr0⟩
  refine
    { toFun := toUnder
      invFun := fun U => (fromUnder U).val
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    let v' : V := (fromUnder (toUnder v)).val
    have hr0 : r.app (Opposite.op ⦋0⦌) v'.val = r.app (Opposite.op ⦋0⦌) v.val :=
      (fromUnder (toUnder v)).property.trans
        ((CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm_apply_apply
          (r.app (Opposite.op ⦋0⦌) v.val))
    have hp' : (SSet.const v'.val : (Δ[0] : SSet.{u}) ⟶ P) ≫ p =
        (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) :=
      (SSet.const_comp v'.val p).trans
        (congrArg (fun t : X _⦋0⦌ => (SSet.const t : (Δ[0] : SSet.{u}) ⟶ X))
          v'.property)
    have hp : (SSet.const v.val : (Δ[0] : SSet.{u}) ⟶ P) ≫ p =
        (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) :=
      (SSet.const_comp v.val p).trans
        (congrArg (fun t : X _⦋0⦌ => (SSet.const t : (Δ[0] : SSet.{u}) ⟶ X))
          v.property)
    have hr : (SSet.const v'.val : (Δ[0] : SSet.{u}) ⟶ P) ≫ r =
        (SSet.const v.val : (Δ[0] : SSet.{u}) ⟶ P) ≫ r :=
      (SSet.const_comp v'.val r).trans
        ((congrArg (fun t : A _⦋0⦌ => (SSet.const t : (Δ[0] : SSet.{u}) ⟶ A)) hr0).trans
          (SSet.const_comp v.val r).symm)
    have hmaps : (SSet.const v'.val : (Δ[0] : SSet.{u}) ⟶ P) =
        (SSet.const v.val : (Δ[0] : SSet.{u}) ⟶ P) :=
      nativeCover_hom_ext (X := X) (x := x) (hp'.trans hp.symm) hr
    have hv : v'.val = v.val :=
      (SSet.yonedaEquiv_const v'.val).symm.trans
        ((congrArg (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)) hmaps).trans
          (SSet.yonedaEquiv_const v.val))
    exact Subtype.ext hv
  · intro U
    have hr0 := (fromUnder U).property
    have hobj : (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
        (r.app (Opposite.op ⦋0⦌) (fromUnder U).val.val) = U.val :=
      (congrArg (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)) hr0).trans
        ((CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).apply_symm_apply U.val)
    exact Subtype.ext hobj

end SSet.KanComplex

namespace CategoryTheory.Under

section Category

variable {C : Type u} [Category.{v} C] (y : C)

/-- The strict object fiber is the original set of arrows from the base object. -/
def objectFiberEquiv (z : C) : {U : Under y // U.right = z} ≃ (y ⟶ z) where
  toFun U := U.val.hom ≫ eqToHom U.prop
  invFun g := ⟨Under.mk g, rfl⟩
  left_inv U := by
    rcases U with ⟨U, hU⟩
    cases hU
    apply Subtype.ext
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  right_inv g := by simp


end Category

end CategoryTheory.Under

namespace SSet.KanComplex

/-- Original vertices over z are the actual native path classes from x to z. -/
noncomputable def nativeCoverVertexPathEquiv
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) :
    {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z} ≃
      (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) :=
  (nativeCoverVertexUnderEquiv (X := X) (x := x) z).trans
    (CategoryTheory.Under.objectFiberEquiv (C := SSet.FundamentalGroupoid X)
      (SSet.FundamentalGroupoid.mk x) (SSet.FundamentalGroupoid.mk z))

/-- The coordinate retains the actual Under arrow and its strict right-endpoint transport. -/
theorem nativeCoverVertexPathEquiv_apply
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    nativeCoverVertexPathEquiv z v =
      (nativeCoverVertexUnderEquiv (X := X) (x := x) z v).val.hom ≫
        eqToHom (nativeCoverVertexUnderEquiv (X := X) (x := x) z v).property := by
  dsimp only [nativeCoverVertexPathEquiv, Equiv.trans, CategoryTheory.Under.objectFiberEquiv]
  rfl

end SSet.KanComplex

namespace SSet.KanComplex

/-- The literal native cover fiber is naturally constant on the original path-class set. -/
noncomputable def nativeCoverFiberPathIso
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) :
    ((Functor.const SimplexCategoryᵒᵖ).obj
      (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z)) ≅
      (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) :=
  ((Functor.const SimplexCategoryᵒᵖ).mapIso
    (nativeCoverVertexPathEquiv (X := X) (x := x) z).symm.toIso) ≪≫
      nativeCoverFiberConstIso (X := X) (x := x) z

/-- A path class gives the actual constant simplex of its reconstructed original cover vertex. -/
theorem nativeCoverFiberPathIso_hom_app
    {X : SSet.{u}} {x : X _⦋0⦌} (z : X _⦋0⦌) (n : ℕ)
    (g : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) :
    (nativeCoverFiberPathIso z).hom.app (Opposite.op ⦋n⦌) g =
      nativeCoverFiberSimplexEquiv z n ((nativeCoverVertexPathEquiv z).symm g) := by
  dsimp only [nativeCoverFiberPathIso, Functor.mapIso, Iso.trans]
  change (nativeCoverFiberConstIso z).hom.app (Opposite.op ⦋n⦌)
      ((nativeCoverVertexPathEquiv z).symm g) =
    nativeCoverFiberSimplexEquiv z n ((nativeCoverVertexPathEquiv z).symm g)
  exact nativeCoverFiberConstIso_hom_app z n ((nativeCoverVertexPathEquiv z).symm g)

end SSet.KanComplex

end

public section

noncomputable section

namespace SSet.KanComplex

private theorem nativeCoverDeck_condition
    {X : SSet.{u}} {x : X _⦋0⦌} :
    nativeCoverProjection X x ≫ nativeCoverUnit X =
      nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x := by
  dsimp only [nativeCover, nativeCoverProjection, nativeCoverUnderProjection] at *
  exact pullback.condition

private theorem nativeCoverDeck_nerve_projection
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    CategoryTheory.nerveMap (CategoryTheory.Under.map (g⁻¹).asHom) ≫
        nativeCoverNerveProjection X x = nativeCoverNerveProjection X x := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let T : CategoryTheory.Under y ⥤ CategoryTheory.Under y :=
    CategoryTheory.Under.map (g⁻¹).asHom
  let F : CategoryTheory.Under y ⥤ Γ := CategoryTheory.Under.forget y
  have hf : T ⋙ F = F := CategoryTheory.Under.mapForget_eq (g⁻¹).asHom
  have hn : CategoryTheory.nerveMap (T ⋙ F) =
      CategoryTheory.nerveMap T ≫ CategoryTheory.nerveMap F :=
    CategoryTheory.nerveFunctor.map_comp T.toCatHom F.toCatHom
  have hq : CategoryTheory.nerveMap T ≫ CategoryTheory.nerveMap F =
      CategoryTheory.nerveMap F :=
    hn.symm.trans
      (congrArg (fun K : CategoryTheory.Under y ⥤ Γ => CategoryTheory.nerveMap K) hf)
  dsimp only [T, F, nativeCoverNerveProjection] at hq ⊢
  exact hq

private theorem nativeCoverDeck_square
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverProjection X x ≫ nativeCoverUnit X =
      (nativeCoverUnderProjection X x ≫
        CategoryTheory.nerveMap (CategoryTheory.Under.map (g⁻¹).asHom)) ≫
          nativeCoverNerveProjection X x := by
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let Y : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid X)
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let q : A ⟶ Y := nativeCoverNerveProjection X x
  let t : A ⟶ A :=
    CategoryTheory.nerveMap (CategoryTheory.Under.map (g⁻¹).asHom)
  have hq : t ≫ q = q := nativeCoverDeck_nerve_projection g
  have hr : (r ≫ t) ≫ q = r ≫ q :=
    (Category.assoc r t q).trans
      (congrArg (fun f : A ⟶ Y => r ≫ f) hq)
  exact (nativeCoverDeck_condition (X := X) (x := x)).trans hr.symm

/-- The actual original pullback deck map uses the saved inverse-End convention. -/
noncomputable def nativeCoverDeckMap
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) : nativeCover X x ⟶ nativeCover X x :=
  pullback.lift (nativeCoverProjection X x)
    (nativeCoverUnderProjection X x ≫
      CategoryTheory.nerveMap (CategoryTheory.Under.map (g⁻¹).asHom))
    (by exact nativeCoverDeck_square g)

/-- The actual deck map preserves the original projection strictly. -/
theorem nativeCoverDeckMap_projection
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverDeckMap g ≫ nativeCoverProjection X x = nativeCoverProjection X x := by
  dsimp only [nativeCoverDeckMap, nativeCoverProjection]
  exact pullback.lift_fst _ _ _

/-- Its actual Under projection is the inverse-precomposition nerve map. -/
theorem nativeCoverDeckMap_underProjection
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverDeckMap g ≫ nativeCoverUnderProjection X x =
      nativeCoverUnderProjection X x ≫
        CategoryTheory.nerveMap (CategoryTheory.Under.map (g⁻¹).asHom) := by
  dsimp only [nativeCoverDeckMap, nativeCoverUnderProjection]
  exact pullback.lift_snd _ _ _

end SSet.KanComplex

namespace SSet.KanComplex

/-- The identity endomorphism gives the actual identity of the original cover. -/
theorem nativeCoverDeckMap_one
    {X : SSet.{u}} {x : X _⦋0⦌} :
    nativeCoverDeckMap (1 : End (SSet.FundamentalGroupoid.mk x)) = 𝟙 (nativeCover X x) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  have he : ((1 : End y)⁻¹).asHom = 𝟙 y := by
    rw [inv_one, End.one_asHom]
  have hf : CategoryTheory.Under.map ((1 : End y)⁻¹).asHom =
      𝟭 (CategoryTheory.Under y) :=
    (congrArg (fun f : y ⟶ y => CategoryTheory.Under.map f) he).trans
      (CategoryTheory.Under.mapId_eq y)
  have hn : CategoryTheory.nerveMap (𝟭 (CategoryTheory.Under y)) = 𝟙 A :=
    CategoryTheory.nerveFunctor.map_id (Cat.of (CategoryTheory.Under y))
  have ht : CategoryTheory.nerveMap (CategoryTheory.Under.map ((1 : End y)⁻¹).asHom) =
      𝟙 A :=
    (congrArg (fun F : CategoryTheory.Under y ⥤ CategoryTheory.Under y =>
      CategoryTheory.nerveMap F) hf).trans hn
  have hp : nativeCoverDeckMap (1 : End y) ≫ p = (𝟙 P) ≫ p :=
    (nativeCoverDeckMap_projection (X := X) (x := x) (1 : End y)).trans
      (Category.id_comp p).symm
  have hr : nativeCoverDeckMap (1 : End y) ≫ r = (𝟙 P) ≫ r :=
    (nativeCoverDeckMap_underProjection (X := X) (x := x) (1 : End y)).trans
      (((congrArg (fun f : A ⟶ A => r ≫ f) ht).trans (Category.comp_id r)).trans
        (Category.id_comp r).symm)
  exact nativeCover_hom_ext (X := X) (x := x) hp hr

/-- Composition is the literal order for applying the original left deck action. -/
theorem nativeCoverDeckMap_mul
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g h : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverDeckMap (g * h) = nativeCoverDeckMap h ≫ nativeCoverDeckMap g := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let p : P ⟶ X := nativeCoverProjection X x
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let Tg : CategoryTheory.Under y ⥤ CategoryTheory.Under y :=
    CategoryTheory.Under.map (g⁻¹).asHom
  let Th : CategoryTheory.Under y ⥤ CategoryTheory.Under y :=
    CategoryTheory.Under.map (h⁻¹).asHom
  let tg : A ⟶ A := CategoryTheory.nerveMap Tg
  let th : A ⟶ A := CategoryTheory.nerveMap Th
  let tgh : A ⟶ A :=
    CategoryTheory.nerveMap (CategoryTheory.Under.map ((g * h)⁻¹).asHom)
  have he : ((g * h)⁻¹).asHom = (g⁻¹).asHom ≫ (h⁻¹).asHom := by
    rw [mul_inv_rev, End.mul_asHom]
  have hf : CategoryTheory.Under.map ((g * h)⁻¹).asHom = Th ⋙ Tg :=
    (congrArg (fun f : y ⟶ y => CategoryTheory.Under.map f) he).trans
      (CategoryTheory.Under.mapComp_eq (g⁻¹).asHom (h⁻¹).asHom)
  have hn : CategoryTheory.nerveMap (Th ⋙ Tg) = th ≫ tg :=
    CategoryTheory.nerveFunctor.map_comp Th.toCatHom Tg.toCatHom
  have ht : tgh = th ≫ tg :=
    (congrArg (fun F : CategoryTheory.Under y ⥤ CategoryTheory.Under y =>
      CategoryTheory.nerveMap F) hf).trans hn
  have hpr : (nativeCoverDeckMap h ≫ nativeCoverDeckMap g) ≫ p = p :=
    (Category.assoc (nativeCoverDeckMap h) (nativeCoverDeckMap g) p).trans
      ((congrArg (fun f : P ⟶ X => nativeCoverDeckMap h ≫ f)
        (nativeCoverDeckMap_projection (X := X) (x := x) g)).trans
          (nativeCoverDeckMap_projection (X := X) (x := x) h))
  have hp : nativeCoverDeckMap (g * h) ≫ p =
      (nativeCoverDeckMap h ≫ nativeCoverDeckMap g) ≫ p :=
    (nativeCoverDeckMap_projection (X := X) (x := x) (g * h)).trans hpr.symm
  have hrl : nativeCoverDeckMap (g * h) ≫ r = r ≫ (th ≫ tg) :=
    (nativeCoverDeckMap_underProjection (X := X) (x := x) (g * h)).trans
      (congrArg (fun f : A ⟶ A => r ≫ f) ht)
  have hrr : (nativeCoverDeckMap h ≫ nativeCoverDeckMap g) ≫ r = r ≫ (th ≫ tg) :=
    (Category.assoc (nativeCoverDeckMap h) (nativeCoverDeckMap g) r).trans
      ((congrArg (fun f : P ⟶ A => nativeCoverDeckMap h ≫ f)
        (nativeCoverDeckMap_underProjection (X := X) (x := x) g)).trans
          ((Category.assoc (nativeCoverDeckMap h) r tg).symm.trans
            ((congrArg (fun f : P ⟶ A => f ≫ tg)
              (nativeCoverDeckMap_underProjection (X := X) (x := x) h)).trans
                (Category.assoc r th tg))))
  exact nativeCover_hom_ext (X := X) (x := x) hp (hrl.trans hrr.symm)

end SSet.KanComplex

namespace SSet.KanComplex

/-- The constructed original deck map is an isomorphism with the forced inverse deck map. -/
noncomputable def nativeCoverDeckIso
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) : nativeCover X x ≅ nativeCover X x where
  hom := nativeCoverDeckMap g
  inv := nativeCoverDeckMap (g⁻¹)
  hom_inv_id := by
    have hm : nativeCoverDeckMap (g⁻¹ * g) =
        nativeCoverDeckMap g ≫ nativeCoverDeckMap (g⁻¹) :=
      nativeCoverDeckMap_mul (X := X) (x := x) (g⁻¹) g
    have h1 : nativeCoverDeckMap (g⁻¹ * g) =
        nativeCoverDeckMap (1 : End (SSet.FundamentalGroupoid.mk x)) :=
      congrArg (fun a : End (SSet.FundamentalGroupoid.mk x) => nativeCoverDeckMap a)
        (inv_mul_cancel g)
    exact hm.symm.trans (h1.trans (nativeCoverDeckMap_one (X := X) (x := x)))
  inv_hom_id := by
    have hm : nativeCoverDeckMap (g * g⁻¹) =
        nativeCoverDeckMap (g⁻¹) ≫ nativeCoverDeckMap g :=
      nativeCoverDeckMap_mul (X := X) (x := x) g (g⁻¹)
    have h1 : nativeCoverDeckMap (g * g⁻¹) =
        nativeCoverDeckMap (1 : End (SSet.FundamentalGroupoid.mk x)) :=
      congrArg (fun a : End (SSet.FundamentalGroupoid.mk x) => nativeCoverDeckMap a)
        (mul_inv_cancel g)
    exact hm.symm.trans (h1.trans (nativeCoverDeckMap_one (X := X) (x := x)))

/-- The isomorphism's forward map is exactly the original constructed deck map. -/
theorem nativeCoverDeckIso_hom
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    (nativeCoverDeckIso g).hom = nativeCoverDeckMap g := by
  dsimp only [nativeCoverDeckIso]

/-- The isomorphism's inverse map is exactly the deck map at the inverse endomorphism. -/
theorem nativeCoverDeckIso_inv
    {X : SSet.{u}} {x : X _⦋0⦌}
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    (nativeCoverDeckIso g).inv = nativeCoverDeckMap (g⁻¹) := by
  dsimp only [nativeCoverDeckIso]

end SSet.KanComplex

namespace SSet.KanComplex

/-- Native first homotopy classes act on actual cover simplices by the constructed deck maps. -/
@[instance_reducible]
noncomputable def nativeCoverPiOneSimplexAction
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (n : ℕ) :
    MulAction (π 1 X x) ((nativeCover X x) _⦋n⦌) := by
  let P : SSet.{u} := nativeCover X x
  let E : Type u := End (SSet.FundamentalGroupoid.mk x)
  letI : MulAction E (P _⦋n⦌) :=
    { smul := fun g s => (nativeCoverDeckMap (X := X) (x := x) g).app (Opposite.op ⦋n⦌) s
      one_smul := by
        intro s
        change (nativeCoverDeckMap (1 : E)).app (Opposite.op ⦋n⦌) s = s
        exact congrArg (fun f : P ⟶ P => f.app (Opposite.op ⦋n⦌) s)
          (nativeCoverDeckMap_one (X := X) (x := x))
      mul_smul := by
        intro g h s
        change (nativeCoverDeckMap (g * h)).app (Opposite.op ⦋n⦌) s =
          (nativeCoverDeckMap g).app (Opposite.op ⦋n⦌)
            ((nativeCoverDeckMap h).app (Opposite.op ⦋n⦌) s)
        exact congrArg (fun f : P ⟶ P => f.app (Opposite.op ⦋n⦌) s)
          (nativeCoverDeckMap_mul (X := X) (x := x) g h) }
  exact MulAction.compHom (P _⦋n⦌) (piOneMulEquivFundamentalGroupoidEnd x).toMonoidHom

/-- The actual simplex actions commute with every original simplicial restriction. -/
theorem nativeCoverPiOneSimplexAction_naturality
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (a : π 1 X x) (s : (nativeCover X x) _⦋n⦌) :
    letI := nativeCoverPiOneSimplexAction x n
    letI := nativeCoverPiOneSimplexAction x m
    (nativeCover X x).map θ.op (a • s) = a • ((nativeCover X x).map θ.op s) := by
  let P : SSet.{u} := nativeCover X x
  let D : P ⟶ P := nativeCoverDeckMap (piOneMulEquivFundamentalGroupoidEnd x a)
  change P.map θ.op (D.app (Opposite.op ⦋n⦌) s) =
    D.app (Opposite.op ⦋m⦌) (P.map θ.op s)
  have hn : P.map θ.op ≫ D.app (Opposite.op ⦋m⦌) =
      D.app (Opposite.op ⦋n⦌) ≫ P.map θ.op := D.naturality θ.op
  have he : D.app (Opposite.op ⦋m⦌) (P.map θ.op s) =
      P.map θ.op (D.app (Opposite.op ⦋n⦌) s) :=
    congrArg (fun f : P _⦋n⦌ ⟶ P _⦋m⦌ => f s) hn
  exact he.symm

/-- Both mandated inversions cancel on an original pointed loop's actual Under projection. -/
theorem nativeCoverPiOneSimplexAction_mk_underProjection
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (n : ℕ)
    (p : X.PtSimplex 1 x) (s : (nativeCover X x) _⦋n⦌) :
    let e : X.Edge x x :=
      SSet.Edge.mk (SSet.yonedaEquiv (SSet.RelativeMorphism.map p))
        (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
        (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
    letI := nativeCoverPiOneSimplexAction x n
    (nativeCoverUnderProjection X x).app (Opposite.op ⦋n⦌) ((π.mk p) • s) =
      (CategoryTheory.nerveMap (CategoryTheory.Under.map (SSet.FundamentalGroupoid.homMk e))).app
        (Opposite.op ⦋n⦌) ((nativeCoverUnderProjection X x).app (Opposite.op ⦋n⦌) s) := by
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} :=
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let e : X.Edge x x :=
    SSet.Edge.mk (SSet.yonedaEquiv (SSet.RelativeMorphism.map p))
      (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
      (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
  let q : End (SSet.FundamentalGroupoid.mk x) :=
    piOneMulEquivFundamentalGroupoidEnd x (π.mk p)
  change r.app (Opposite.op ⦋n⦌) ((nativeCoverDeckMap q).app (Opposite.op ⦋n⦌) s) =
    (CategoryTheory.nerveMap (CategoryTheory.Under.map (SSet.FundamentalGroupoid.homMk e))).app
      (Opposite.op ⦋n⦌) (r.app (Opposite.op ⦋n⦌) s)
  have hr : nativeCoverDeckMap q ≫ r =
      r ≫ CategoryTheory.nerveMap (CategoryTheory.Under.map (q⁻¹).asHom) :=
    nativeCoverDeckMap_underProjection (X := X) (x := x) q
  have heval : r.app (Opposite.op ⦋n⦌)
        ((nativeCoverDeckMap q).app (Opposite.op ⦋n⦌) s) =
      (CategoryTheory.nerveMap (CategoryTheory.Under.map (q⁻¹).asHom)).app
        (Opposite.op ⦋n⦌) (r.app (Opposite.op ⦋n⦌) s) :=
    congrArg (fun f : P ⟶ A => f.app (Opposite.op ⦋n⦌) s) hr
  have hinv : (q⁻¹).asHom = SSet.FundamentalGroupoid.homMk e := by
    dsimp only [q]
    rw [piOneMulEquivFundamentalGroupoidEnd_mk]
    change Groupoid.inv (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk e)) =
      SSet.FundamentalGroupoid.homMk e
    rw [Groupoid.inv_eq_inv, IsIso.inv_inv]
  have hn : CategoryTheory.nerveMap (CategoryTheory.Under.map (q⁻¹).asHom) =
      CategoryTheory.nerveMap (CategoryTheory.Under.map (SSet.FundamentalGroupoid.homMk e)) :=
    congrArg (fun f : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk x =>
      CategoryTheory.nerveMap (CategoryTheory.Under.map f)) hinv
  have htarget : (CategoryTheory.nerveMap (CategoryTheory.Under.map (q⁻¹).asHom)).app
        (Opposite.op ⦋n⦌) (r.app (Opposite.op ⦋n⦌) s) =
      (CategoryTheory.nerveMap (CategoryTheory.Under.map (SSet.FundamentalGroupoid.homMk e))).app
        (Opposite.op ⦋n⦌) (r.app (Opposite.op ⦋n⦌) s) :=
    congrArg (fun f : A ⟶ A => f.app (Opposite.op ⦋n⦌) (r.app (Opposite.op ⦋n⦌) s)) hn
  exact heval.trans htarget

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual native first-homotopy action preserves the original base projection
in every degree. -/
theorem nativeCoverPiOneSimplexAction_projection
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (n : ℕ)
    (a : π 1 X x) (s : (nativeCover X x) _⦋n⦌) :
    letI := nativeCoverPiOneSimplexAction x n
    (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) (a • s) =
      (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) s := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let D : P ⟶ P := nativeCoverDeckMap (piOneMulEquivFundamentalGroupoidEnd x a)
  change p.app (Opposite.op ⦋n⦌) (D.app (Opposite.op ⦋n⦌) s) =
    p.app (Opposite.op ⦋n⦌) s
  have hp : D ≫ p = p :=
    nativeCoverDeckMap_projection (X := X) (x := x)
      (piOneMulEquivFundamentalGroupoidEnd x a)
  exact congrArg (fun f : P ⟶ X => f.app (Opposite.op ⦋n⦌) s) hp

/-- The actual cover-vertex action restricts to each literal vertex fiber. -/
@[instance_reducible]
noncomputable def nativeCoverPiOneVertexFiberAction
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) :
    MulAction (π 1 X x)
      {v : (nativeCover X x) _⦋0⦌ //
        (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z} := by
  letI := nativeCoverPiOneSimplexAction x 0
  exact
    { smul := fun a v =>
        ⟨a • v.val,
          (nativeCoverPiOneSimplexAction_projection x 0 a v.val).trans v.property⟩
      one_smul := by
        intro v
        apply Subtype.ext
        exact one_smul (π 1 X x) v.val
      mul_smul := by
        intro a b v
        apply Subtype.ext
        exact mul_smul a b v.val }

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual vertex-fiber action agrees with original native-path inverse-End precomposition. -/
theorem nativeCoverVertexPathEquiv_smul
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌)
    (a : π 1 X x)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    letI := nativeCoverPiOneVertexFiberAction x z
    nativeCoverVertexPathEquiv z (a • v) =
      ((piOneMulEquivFundamentalGroupoidEnd x a)⁻¹).asHom ≫ nativeCoverVertexPathEquiv z v := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let zz : Γ := SSet.FundamentalGroupoid.mk z
  let P : SSet.{u} := nativeCover X x
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let Vz : Type u := {v : P _⦋0⦌ //
    (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  let W : Type u := {U : CategoryTheory.Under y // U.right = zz}
  let := nativeCoverPiOneVertexFiberAction x z
  let w : Vz := a • v
  let U : W := nativeCoverVertexUnderEquiv (X := X) (x := x) z v
  let Uact : W := nativeCoverVertexUnderEquiv (X := X) (x := x) z w
  let g : End y := piOneMulEquivFundamentalGroupoidEnd x a
  let T : CategoryTheory.Under y ⥤ CategoryTheory.Under y :=
    CategoryTheory.Under.map (g⁻¹).asHom
  let t : A ⟶ A := CategoryTheory.nerveMap T
  let Umap : W := ⟨T.obj U.val, U.property⟩
  let eF : W ≃ (y ⟶ zz) := CategoryTheory.Under.objectFiberEquiv y zz
  have hU : U.val = (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
      (r.app (Opposite.op ⦋0⦌) v.val) := by
    dsimp only [U, nativeCoverVertexUnderEquiv, r] ; rfl
  have hUact : Uact.val = (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y))
      (r.app (Opposite.op ⦋0⦌) w.val) := by
    dsimp only [Uact, nativeCoverVertexUnderEquiv, r] ; rfl
  have hr : r.app (Opposite.op ⦋0⦌) w.val =
      t.app (Opposite.op ⦋0⦌) (r.app (Opposite.op ⦋0⦌) v.val) := by
    change r.app (Opposite.op ⦋0⦌) ((nativeCoverDeckMap g).app (Opposite.op ⦋0⦌) v.val) =
      t.app (Opposite.op ⦋0⦌) (r.app (Opposite.op ⦋0⦌) v.val)
    exact congrArg (fun f : P ⟶ A => f.app (Opposite.op ⦋0⦌) v.val)
      (nativeCoverDeckMap_underProjection (X := X) (x := x) g)
  have hv : (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm U.val =
      r.app (Opposite.op ⦋0⦌) v.val :=
    (congrArg (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm hU).trans
      ((CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm_apply_apply
        (r.app (Opposite.op ⦋0⦌) v.val))
  have ht0 : t.app (Opposite.op ⦋0⦌)
        ((CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm U.val) =
      (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm (T.obj U.val) :=
    CategoryTheory.nerveMap_app_mk₀ T U.val
  have hmap : t.app (Opposite.op ⦋0⦌) (r.app (Opposite.op ⦋0⦌) v.val) =
      (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm (T.obj U.val) :=
    (congrArg (fun b : A _⦋0⦌ => t.app (Opposite.op ⦋0⦌) b) hv).symm.trans ht0
  have hobj : Uact.val = T.obj U.val :=
    hUact.trans
      ((congrArg (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)) hr).trans
        ((congrArg (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)) hmap).trans
          ((CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).apply_symm_apply
            (T.obj U.val))))
  have hsub : Uact = Umap := Subtype.ext hobj
  have hpv : nativeCoverVertexPathEquiv z v = eF U := by
    dsimp only [eF, CategoryTheory.Under.objectFiberEquiv]
    exact nativeCoverVertexPathEquiv_apply z v
  have hpw : nativeCoverVertexPathEquiv z w = eF Uact := by
    dsimp only [eF, CategoryTheory.Under.objectFiberEquiv]
    exact nativeCoverVertexPathEquiv_apply z w
  have hpre : eF Umap = (g⁻¹).asHom ≫ eF U := by
    change ((g⁻¹).asHom ≫ U.val.hom) ≫ eqToHom U.property =
      (g⁻¹).asHom ≫ (U.val.hom ≫ eqToHom U.property)
    exact Category.assoc _ _ _
  exact hpw.trans
    ((congrArg (fun Q : W => eF Q) hsub).trans
      (hpre.trans (congrArg (fun f : y ⟶ zz => (g⁻¹).asHom ≫ f) hpv.symm)))

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual native first-homotopy action has injective orbits on each original vertex fiber. -/
theorem nativeCoverPiOneVertexFiberAction_free
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    letI := nativeCoverPiOneVertexFiberAction x z
    Function.Injective (fun a : π 1 X x => a • v) := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let Vz : Type u := {v : (nativeCover X x) _⦋0⦌ //
    (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  let := nativeCoverPiOneVertexFiberAction x z
  let ψ : π 1 X x ≃* End y := piOneMulEquivFundamentalGroupoidEnd x
  let Φ := nativeCoverVertexPathEquiv (X := X) (x := x) z
  intro a b hab
  have ha : Φ (a • v) = ((ψ a)⁻¹).asHom ≫ Φ v :=
    nativeCoverVertexPathEquiv_smul x z a v
  have hb : Φ (b • v) = ((ψ b)⁻¹).asHom ≫ Φ v :=
    nativeCoverVertexPathEquiv_smul x z b v
  have he : ((ψ a)⁻¹).asHom ≫ Φ v = ((ψ b)⁻¹).asHom ≫ Φ v :=
    ha.symm.trans ((congrArg (fun w : Vz => Φ w) hab).trans hb)
  have hi : (ψ a)⁻¹ = (ψ b)⁻¹ := by
    apply End.ext
    exact (cancel_mono (Φ v)).mp he
  have hψ : ψ a = ψ b :=
    (inv_inv (ψ a)).symm.trans
      ((congrArg (fun g : End y => g⁻¹) hi).trans (inv_inv (ψ b)))
  exact ψ.injective hψ

/-- For any two actual fiber vertices, one unique native class carries the first to the second. -/
theorem nativeCoverPiOneVertexFiberAction_existsUnique
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌)
    (v w : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    letI := nativeCoverPiOneVertexFiberAction x z
    ∃! a : π 1 X x, a • v = w := by
  let Γ : Type u := SSet.FundamentalGroupoid X
  let y : Γ := SSet.FundamentalGroupoid.mk x
  let zz : Γ := SSet.FundamentalGroupoid.mk z
  let := nativeCoverPiOneVertexFiberAction x z
  let ψ : π 1 X x ≃* End y := piOneMulEquivFundamentalGroupoidEnd x
  let Φ := nativeCoverVertexPathEquiv (X := X) (x := x) z
  let fv : y ⟶ zz := Φ v
  let fw : y ⟶ zz := Φ w
  let g : End y := End.of (fw ≫ CategoryTheory.inv fv)
  let a : π 1 X x := ψ.symm (g⁻¹)
  have hψ : ψ a = g⁻¹ := ψ.apply_symm_apply (g⁻¹)
  have hi : (ψ a)⁻¹ = g :=
    (congrArg (fun b : End y => b⁻¹) hψ).trans (inv_inv g)
  have hc : g.asHom ≫ fv = fw := by
    change (fw ≫ CategoryTheory.inv fv) ≫ fv = fw
    exact (Category.assoc fw (CategoryTheory.inv fv) fv).trans
      ((congrArg (fun f : zz ⟶ zz => fw ≫ f) (IsIso.inv_hom_id fv)).trans
        (Category.comp_id fw))
  have hΦ : Φ (a • v) = Φ w :=
    (nativeCoverVertexPathEquiv_smul x z a v).trans
      ((congrArg (fun b : End y => b.asHom ≫ fv) hi).trans hc)
  have ha : a • v = w := Φ.injective hΦ
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact (nativeCoverPiOneVertexFiberAction_free x z v) (hb.trans ha.symm)

end SSet.KanComplex

end

public section

noncomputable section

namespace SSet.KanComplex

/-- The constructed native action restricts to every simplex of the literal original fiber. -/
@[instance_reducible]
noncomputable def nativeCoverPiOneFiberSimplexAction
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) (n : ℕ) :
    MulAction (π 1 X x)
      ((SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  letI := nativeCoverPiOneSimplexAction x n
  exact
    { smul := fun a s => ⟨a • s.val, by
        apply (SSet.Subcomplex.mem_fiber_obj_iff p z).mpr
        have hp : p.app (Opposite.op ⦋n⦌) (a • s.val) =
            p.app (Opposite.op ⦋n⦌) s.val :=
          nativeCoverPiOneSimplexAction_projection x n a s.val
        rw [hp]
        exact (SSet.Subcomplex.mem_fiber_obj_iff p z).mp s.property⟩
      one_smul := by
        intro s
        apply Subtype.ext
        exact one_smul (π 1 X x) s.val
      mul_smul := by
        intro a b s
        apply Subtype.ext
        exact mul_smul a b s.val }

/-- The actual fiber actions commute with every original simplicial restriction. -/
theorem nativeCoverPiOneFiberSimplexAction_naturality
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (a : π 1 X x)
    (s : (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) :
    letI := nativeCoverPiOneFiberSimplexAction x z n
    letI := nativeCoverPiOneFiberSimplexAction x z m
    (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}).map θ.op (a • s) =
      a • ((SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}).map θ.op s) := by
  let := nativeCoverPiOneSimplexAction x n
  let := nativeCoverPiOneSimplexAction x m
  apply Subtype.ext
  change (nativeCover X x).map θ.op (a • s.val) =
    a • ((nativeCover X x).map θ.op s.val)
  exact nativeCoverPiOneSimplexAction_naturality x θ a s.val

/-- The proved constant-simplex component equivalence respects the actual fiber actions. -/
theorem nativeCoverFiberSimplexEquiv_smul
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) (n : ℕ)
    (a : π 1 X x)
    (v : {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    letI := nativeCoverPiOneVertexFiberAction x z
    letI := nativeCoverPiOneFiberSimplexAction x z n
    nativeCoverFiberSimplexEquiv z n (a • v) = a • (nativeCoverFiberSimplexEquiv z n v) := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let F : SSet.{u} := (SSet.Subcomplex.fiber p z : SSet.{u})
  let V : Type u := {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z}
  let θ : ⦋n⦌ ⟶ ⦋0⦌ := SimplexCategory.const ⦋n⦌ ⦋0⦌ (0 : Fin 1)
  let := nativeCoverPiOneSimplexAction x 0
  let := nativeCoverPiOneSimplexAction x n
  let := nativeCoverPiOneVertexFiberAction x z
  let := nativeCoverPiOneFiberSimplexAction x z n
  have hE (w : V) : (nativeCoverFiberSimplexEquiv z n w).val =
      P.map θ.op w.val := by
    let wF : F _⦋0⦌ :=
      ⟨w.val, (SSet.Subcomplex.mem_fiber_obj_zero_iff p z).mpr w.property⟩
    let c : (Δ[0] : SSet.{u}) ⟶ F := SSet.const wF
    have hcn : nativeCoverFiberSimplexEquiv z n w =
        (SSet.yonedaEquiv (X := F) (n := ⦋n⦌))
          (SSet.const wF : (Δ[n] : SSet.{u}) ⟶ F) :=
      nativeCoverFiberSimplexEquiv_apply z n w
    have hn : F.map θ.op ((SSet.yonedaEquiv (X := F) (n := ⦋0⦌)) c) =
        (SSet.yonedaEquiv (X := F) (n := ⦋n⦌)) (SSet.stdSimplex.map θ ≫ c) :=
      SSet.yonedaEquiv_naturality θ c
    have hc : SSet.stdSimplex.map θ ≫ c =
        (SSet.const wF : (Δ[n] : SSet.{u}) ⟶ F) :=
      SSet.comp_const (SSet.stdSimplex.map θ) wF
    have h0 : (SSet.yonedaEquiv (X := F) (n := ⦋0⦌)) c = wF :=
      SSet.yonedaEquiv_const wF
    have hm : F.map θ.op wF = nativeCoverFiberSimplexEquiv z n w :=
      (congrArg (fun t : F _⦋0⦌ => F.map θ.op t) h0).symm.trans
        (hn.trans
          ((congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ F =>
            (SSet.yonedaEquiv (X := F) (n := ⦋n⦌)) f) hc).trans hcn.symm))
    exact congrArg (fun s : F _⦋n⦌ => s.val) hm.symm
  apply Subtype.ext
  change (nativeCoverFiberSimplexEquiv z n (a • v)).val =
    a • (nativeCoverFiberSimplexEquiv z n v).val
  rw [hE (a • v), hE v]
  change P.map θ.op (a • v.val) = a • (P.map θ.op v.val)
  exact nativeCoverPiOneSimplexAction_naturality x θ a v.val

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual native action has injective orbits on every literal fiber-simplex set. -/
theorem nativeCoverPiOneFiberSimplexAction_free
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) (n : ℕ)
    (s : (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) :
    letI := nativeCoverPiOneFiberSimplexAction x z n
    Function.Injective (fun a : π 1 X x => a • s) := by
  let V : Type u := {v : (nativeCover X x) _⦋0⦌ //
    (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  let F : SSet.{u} := (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u})
  let e : V ≃ F _⦋n⦌ := nativeCoverFiberSimplexEquiv z n
  let := nativeCoverPiOneVertexFiberAction x z
  let := nativeCoverPiOneFiberSimplexAction x z n
  let v : V := e.symm s
  have hv : e v = s := e.apply_symm_apply s
  intro a b hab
  have ha : e (a • v) = a • s :=
    (nativeCoverFiberSimplexEquiv_smul x z n a v).trans
      (congrArg (fun t : F _⦋n⦌ => a • t) hv)
  have hb : e (b • v) = b • s :=
    (nativeCoverFiberSimplexEquiv_smul x z n b v).trans
      (congrArg (fun t : F _⦋n⦌ => b • t) hv)
  have he : e (a • v) = e (b • v) := ha.trans (hab.trans hb.symm)
  exact (nativeCoverPiOneVertexFiberAction_free x z v) (e.injective he)

/-- One unique native class carries any given literal fiber simplex to any other. -/
theorem nativeCoverPiOneFiberSimplexAction_existsUnique
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) (n : ℕ)
    (s t : (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) :
    letI := nativeCoverPiOneFiberSimplexAction x z n
    ∃! a : π 1 X x, a • s = t := by
  let V : Type u := {v : (nativeCover X x) _⦋0⦌ //
    (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}
  let F : SSet.{u} := (SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u})
  let e : V ≃ F _⦋n⦌ := nativeCoverFiberSimplexEquiv z n
  let := nativeCoverPiOneVertexFiberAction x z
  let := nativeCoverPiOneFiberSimplexAction x z n
  let v : V := e.symm s
  let w : V := e.symm t
  have hv : e v = s := e.apply_symm_apply s
  have hw : e w = t := e.apply_symm_apply t
  obtain ⟨a, ha, _⟩ := nativeCoverPiOneVertexFiberAction_existsUnique x z v w
  have he : a • s = t :=
    (congrArg (fun q : F _⦋n⦌ => a • q) hv).symm.trans
      ((nativeCoverFiberSimplexEquiv_smul x z n a v).symm.trans
        ((congrArg (fun q : V => e q) ha).trans hw))
  refine ⟨a, he, ?_⟩
  intro b hb
  exact (nativeCoverPiOneFiberSimplexAction_free x z n s) (hb.trans he.symm)

/-- A literal fiber has simplices exactly over the original basepoint's component. -/
theorem nativeCover_fiber_simplex_nonempty_iff_piZero_eq
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (z : X _⦋0⦌) (n : ℕ) :
    Nonempty ((SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) ↔
      SSet.π₀.mk x = SSet.π₀.mk z := by
  classical
  constructor
  · rintro ⟨s⟩
    let v := (nativeCoverFiberSimplexEquiv (X := X) (x := x) z n).symm s
    let γ : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z :=
      nativeCoverVertexPathEquiv (X := X) (x := x) z v
    obtain ⟨e, _⟩ := SSet.FundamentalGroupoid.homMk_surjective (x := x) (y := z) γ
    exact SSet.π₀.sound e
  · intro h₀
    have h : Relation.EqvGen (SSet.π₀Rel (X := X)) x z :=
      (SSet.π₀.mk_eq_mk_iff x z).mp h₀
    have hΓ : Nonempty
        (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) := by
      clear h₀
      induction h with
      | rel _ _ hab =>
          obtain ⟨e⟩ := hab
          exact ⟨SSet.FundamentalGroupoid.homMk e⟩
      | refl a => exact ⟨𝟙 (SSet.FundamentalGroupoid.mk a)⟩
      | symm _ _ _ ih => exact ⟨CategoryTheory.inv ih.some⟩
      | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some ≫ ih₂.some⟩
    let v := (nativeCoverVertexPathEquiv (X := X) (x := x) z).symm hΓ.some
    exact ⟨nativeCoverFiberSimplexEquiv (X := X) (x := x) z n v⟩

/-- Every degree of each literal fiber is inhabited when the original Kan base is connected. -/
theorem nativeCover_fiber_simplex_nonempty
    {X : SSet.{u}} [SSet.KanComplex X] [X.IsConnected]
    (x : X _⦋0⦌) (z : X _⦋0⦌) (n : ℕ) :
    Nonempty ((SSet.Subcomplex.fiber (nativeCoverProjection X x) z : SSet.{u}) _⦋n⦌) := by
  exact (nativeCover_fiber_simplex_nonempty_iff_piZero_eq x z n).mpr
    (Subsingleton.elim _ _)

end SSet.KanComplex

namespace SSet.KanComplex

/-- The actual native action has injective orbits on all original cover simplices. -/
theorem nativeCoverPiOneSimplexAction_free
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (n : ℕ)
    (s : (nativeCover X x) _⦋n⦌) :
    letI := nativeCoverPiOneSimplexAction x n
    Function.Injective (fun a : π 1 X x => a • s) := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ (0 : Fin (n + 1))
  let s0 : P _⦋0⦌ := P.map θ.op s
  let z : X _⦋0⦌ := p.app (Opposite.op ⦋0⦌) s0
  let V : Type u := {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z}
  let v : V := ⟨s0, rfl⟩
  let := nativeCoverPiOneSimplexAction x n
  let := nativeCoverPiOneSimplexAction x 0
  let := nativeCoverPiOneVertexFiberAction x z
  intro a b hab
  have ha : P.map θ.op (a • s) = a • s0 :=
    nativeCoverPiOneSimplexAction_naturality x θ a s
  have hb : P.map θ.op (b • s) = b • s0 :=
    nativeCoverPiOneSimplexAction_naturality x θ b s
  have h0 : a • s0 = b • s0 := ha.symm.trans
    ((congrArg (fun t : P _⦋n⦌ => P.map θ.op t) hab).trans hb)
  have hv : a • v = b • v := Subtype.ext h0
  exact (nativeCoverPiOneVertexFiberAction_free x z v) hv

/-- One unique native class carries any original cover simplex to another over the same base. -/
theorem nativeCoverPiOneSimplexAction_existsUnique_of_projection_eq
    {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) (n : ℕ)
    (s t : (nativeCover X x) _⦋n⦌)
    (hst : (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) s =
      (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) t) :
    letI := nativeCoverPiOneSimplexAction x n
    ∃! a : π 1 X x, a • s = t := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let w0 : (Δ[n] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  let θ : ⦋0⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.objEquiv w0
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm w0
  have hα : α = SSet.stdSimplex.map θ := by
    apply (SSet.yonedaEquiv (X := (Δ[n] : SSet.{u})) (n := ⦋0⦌)).injective
    have ha : (SSet.yonedaEquiv (X := (Δ[n] : SSet.{u})) (n := ⦋0⦌)) α = w0 :=
      (SSet.yonedaEquiv (X := (Δ[n] : SSet.{u})) (n := ⦋0⦌)).apply_symm_apply w0
    have ht : (SSet.yonedaEquiv (X := (Δ[n] : SSet.{u})) (n := ⦋0⦌))
        (SSet.stdSimplex.map θ) = w0 :=
      (SSet.yonedaEquiv_map θ).trans (SSet.stdSimplex.objEquiv.symm_apply_apply w0)
    exact ha.trans ht.symm
  let s0 : P _⦋0⦌ := P.map θ.op s
  let t0 : P _⦋0⦌ := P.map θ.op t
  let z : X _⦋0⦌ := p.app (Opposite.op ⦋0⦌) s0
  have hps : p.app (Opposite.op ⦋0⦌) s0 = X.map θ.op (p.app (Opposite.op ⦋n⦌) s) :=
    congrArg (fun f : P _⦋n⦌ ⟶ X _⦋0⦌ => f s) (p.naturality θ.op)
  have hpt : p.app (Opposite.op ⦋0⦌) t0 = X.map θ.op (p.app (Opposite.op ⦋n⦌) t) :=
    congrArg (fun f : P _⦋n⦌ ⟶ X _⦋0⦌ => f t) (p.naturality θ.op)
  have hp0 : p.app (Opposite.op ⦋0⦌) s0 = p.app (Opposite.op ⦋0⦌) t0 :=
    hps.trans ((congrArg (fun q : X _⦋n⦌ => X.map θ.op q) hst).trans hpt.symm)
  let V : Type u := {v : P _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = z}
  let v : V := ⟨s0, rfl⟩
  let w : V := ⟨t0, hp0.symm⟩
  let := nativeCoverPiOneSimplexAction x n
  let := nativeCoverPiOneSimplexAction x 0
  let := nativeCoverPiOneVertexFiberAction x z
  obtain ⟨a, ha, _⟩ := nativeCoverPiOneVertexFiberAction_existsUnique x z v w
  have ha0 : a • s0 = t0 := congrArg (fun q : V => q.val) ha
  have hfirst0 : P.map θ.op (a • s) = t0 :=
    (nativeCoverPiOneSimplexAction_naturality x θ a s).trans ha0
  let A : (Δ[n] : SSet.{u}) ⟶ P :=
    (SSet.yonedaEquiv (X := P) (n := ⦋n⦌)).symm (a • s)
  let B : (Δ[n] : SSet.{u}) ⟶ P :=
    (SSet.yonedaEquiv (X := P) (n := ⦋n⦌)).symm t
  let σ : (Δ[n] : SSet.{u}) ⟶ X := B ≫ p
  have hAp : A ≫ p = σ := by
    apply (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).injective
    have hA : (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) (A ≫ p) =
        p.app (Opposite.op ⦋n⦌) (a • s) :=
      (SSet.yonedaEquiv_comp A p).trans
        (congrArg (fun q : P _⦋n⦌ => p.app (Opposite.op ⦋n⦌) q)
          ((SSet.yonedaEquiv (X := P) (n := ⦋n⦌)).apply_symm_apply (a • s)))
    have hB : (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) (B ≫ p) =
        p.app (Opposite.op ⦋n⦌) t :=
      (SSet.yonedaEquiv_comp B p).trans
        (congrArg (fun q : P _⦋n⦌ => p.app (Opposite.op ⦋n⦌) q)
          ((SSet.yonedaEquiv (X := P) (n := ⦋n⦌)).apply_symm_apply t))
    exact hA.trans ((nativeCoverPiOneSimplexAction_projection x n a s).trans
      (hst.trans hB.symm))
  have hNA : SSet.stdSimplex.map θ ≫ A =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm (P.map θ.op (a • s)) :=
    SSet.yonedaEquiv_symm_naturality_left θ (a • s)
  have hNB : SSet.stdSimplex.map θ ≫ B =
      (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm t0 :=
    SSet.yonedaEquiv_symm_naturality_left θ t
  have hfirstA : α ≫ A = (SSet.const t0 : (Δ[0] : SSet.{u}) ⟶ P) :=
    (congrArg (fun i : (Δ[0] : SSet.{u}) ⟶ Δ[n] => i ≫ A) hα).trans
      (hNA.trans
        ((congrArg (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm hfirst0).trans
          (SSet.yonedaEquiv_symm_zero t0)))
  have hfirstB : α ≫ B = (SSet.const t0 : (Δ[0] : SSet.{u}) ⟶ P) :=
    (congrArg (fun i : (Δ[0] : SSet.{u}) ⟶ Δ[n] => i ≫ B) hα).trans
      (hNB.trans (SSet.yonedaEquiv_symm_zero t0))
  have hv : α ≫ σ =
      (SSet.const (p.app (Opposite.op ⦋0⦌) t0) : (Δ[0] : SSet.{u}) ⟶ X) :=
    (Category.assoc α B p).symm.trans
      ((congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ P => f ≫ p) hfirstB).trans
        (SSet.const_comp t0 p))
  obtain ⟨W, _, hUnique⟩ := existsUnique_nativeCoverSimplexLiftFromFirst σ t0 hv
  have hAB : A = B := (hUnique A ⟨hAp, hfirstA⟩).trans
    (hUnique B ⟨rfl, hfirstB⟩).symm
  have hat : a • s = t :=
    ((SSet.yonedaEquiv (X := P) (n := ⦋n⦌)).apply_symm_apply (a • s)).symm.trans
      ((congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ P =>
        (SSet.yonedaEquiv (X := P) (n := ⦋n⦌)) f) hAB).trans
          ((SSet.yonedaEquiv (X := P) (n := ⦋n⦌)).apply_symm_apply t))
  refine ⟨a, hat, ?_⟩
  intro b hb
  exact (nativeCoverPiOneSimplexAction_free x n s) (hb.trans hat.symm)

end SSet.KanComplex

namespace SSet.KanComplex

/-- Over a connected Kan base, every original vertex fiber has an actual cover vertex. -/
theorem nativeCover_vertexFiber_nonempty
    {X : SSet.{u}} [X.IsConnected] {x : X _⦋0⦌}
    (z : X _⦋0⦌) :
    Nonempty {v : (nativeCover X x) _⦋0⦌ //
      (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z} := by
  classical
  have h₀ : SSet.π₀.mk x = SSet.π₀.mk z := Subsingleton.elim _ _
  have h : Relation.EqvGen (SSet.π₀Rel (X := X)) x z :=
    (SSet.π₀.mk_eq_mk_iff x z).mp h₀
  have hΓ : Nonempty
      (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) := by
    clear h₀
    induction h with
    | rel _ _ hab =>
        obtain ⟨e⟩ := hab
        exact ⟨SSet.FundamentalGroupoid.homMk e⟩
    | refl a => exact ⟨𝟙 (SSet.FundamentalGroupoid.mk a)⟩
    | symm _ _ _ ih => exact ⟨CategoryTheory.inv ih.some⟩
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some ≫ ih₂.some⟩
  exact ⟨(nativeCoverVertexPathEquiv (X := X) (x := x) z).symm hΓ.some⟩

/-- The original cover projection is onto the vertices of a connected Kan base. -/
theorem nativeCoverProjection_app_zero_surjective
    {X : SSet.{u}} [X.IsConnected] (x : X _⦋0⦌) :
    Function.Surjective
      ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌)) := by
  intro z
  obtain ⟨v⟩ := nativeCover_vertexFiber_nonempty (X := X) (x := x) z
  exact ⟨v.val, v.property⟩

end SSet.KanComplex

namespace SSet.KanComplex

/-- The original cover projection is onto every simplex degree of a connected Kan base. -/
theorem nativeCoverProjection_app_surjective
    {X : SSet.{u}} [X.IsConnected] (x : X _⦋0⦌) (n : ℕ) :
    Function.Surjective
      ((nativeCoverProjection X x).app (Opposite.op ⦋n⦌)) := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  intro s
  let σ : (Δ[n] : SSet.{u}) ⟶ X :=
    (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).symm s
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))
  let z : X _⦋0⦌ := (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (α ≫ σ)
  obtain ⟨v, hpv⟩ := nativeCoverProjection_app_zero_surjective x z
  have hα : α ≫ σ = (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) :=
    ((SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm_apply_apply (α ≫ σ)).symm.trans
      (SSet.yonedaEquiv_symm_zero z)
  have hv : α ≫ σ =
      (SSet.const (p.app (Opposite.op ⦋0⦌) v) : (Δ[0] : SSet.{u}) ⟶ X) :=
    hα.trans (congrArg (fun w : X _⦋0⦌ =>
      (SSet.const w : (Δ[0] : SSet.{u}) ⟶ X)) hpv.symm)
  let L : (Δ[n] : SSet.{u}) ⟶ P := nativeCoverSimplexLiftFromFirstMap σ v hv
  have hL : L ≫ p = σ := nativeCoverSimplexLiftFromFirstMap_projection σ v hv
  have hσ : (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) σ = s :=
    (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).apply_symm_apply s
  refine ⟨(SSet.yonedaEquiv (X := P) (n := ⦋n⦌)) L, ?_⟩
  exact (SSet.yonedaEquiv_comp L p).symm.trans
    ((congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X =>
      (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) f) hL).trans hσ)

end SSet.KanComplex

namespace SSet.KanComplex

/-- Reindexing the original lift is canonical from its actual changed first cover vertex. -/
theorem nativeCoverSimplexLiftFromFirstMap_reindex
    {X : SSet.{u}} {x : X _⦋0⦌} {m n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ X) (v : (nativeCover X x) _⦋0⦌)
    (hv : (SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]) ≫ σ =
      (SSet.const ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v) :
        (Δ[0] : SSet.{u}) ⟶ X))
    (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    let L : (Δ[n] : SSet.{u}) ⟶ nativeCover X x :=
      nativeCoverSimplexLiftFromFirstMap σ v hv
    let R : (Δ[m] : SSet.{u}) ⟶ nativeCover X x := SSet.stdSimplex.map θ ≫ L
    let σθ : (Δ[m] : SSet.{u}) ⟶ X := SSet.stdSimplex.map θ ≫ σ
    let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)))
    let vθ : (nativeCover X x) _⦋0⦌ :=
      (SSet.yonedaEquiv (X := nativeCover X x) (n := ⦋0⦌)) (α ≫ R)
    ∃ hvθ : α ≫ σθ =
        (SSet.const ((nativeCoverProjection X x).app (Opposite.op ⦋0⦌) vθ) :
          (Δ[0] : SSet.{u}) ⟶ X),
      R = nativeCoverSimplexLiftFromFirstMap σθ vθ hvθ := by
  let P : SSet.{u} := nativeCover X x
  let p : P ⟶ X := nativeCoverProjection X x
  let L : (Δ[n] : SSet.{u}) ⟶ P := nativeCoverSimplexLiftFromFirstMap σ v hv
  let R : (Δ[m] : SSet.{u}) ⟶ P := SSet.stdSimplex.map θ ≫ L
  let σθ : (Δ[m] : SSet.{u}) ⟶ X := SSet.stdSimplex.map θ ≫ σ
  let α : (Δ[0] : SSet.{u}) ⟶ Δ[m] := SSet.yonedaEquiv.symm
    (SSet.stdSimplex.obj₀Equiv.symm (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)))
  let vθ : P _⦋0⦌ := (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)) (α ≫ R)
  change ∃ hvθ : α ≫ σθ =
      (SSet.const (p.app (Opposite.op ⦋0⦌) vθ) : (Δ[0] : SSet.{u}) ⟶ X),
    R = nativeCoverSimplexLiftFromFirstMap σθ vθ hvθ
  have hLp : L ≫ p = σ := nativeCoverSimplexLiftFromFirstMap_projection σ v hv
  have hRp : R ≫ p = σθ :=
    (Category.assoc (SSet.stdSimplex.map θ) L p).trans
      (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ X => SSet.stdSimplex.map θ ≫ f) hLp)
  have hq : (α ≫ R) ≫ p = α ≫ σθ :=
    (Category.assoc α R p).trans
      (congrArg (fun f : (Δ[m] : SSet.{u}) ⟶ X => α ≫ f) hRp)
  have hz : (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (α ≫ σθ) =
      p.app (Opposite.op ⦋0⦌) vθ :=
    (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ X =>
      (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) f) hq).symm.trans
        (SSet.yonedaEquiv_comp (α ≫ R) p)
  have hvθ : α ≫ σθ =
      (SSet.const (p.app (Opposite.op ⦋0⦌) vθ) : (Δ[0] : SSet.{u}) ⟶ X) :=
    (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).injective
      (hz.trans (SSet.yonedaEquiv_const (p.app (Opposite.op ⦋0⦌) vθ)).symm)
  have hfirst : α ≫ R = (SSet.const vθ : (Δ[0] : SSet.{u}) ⟶ P) :=
    ((SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm_apply_apply (α ≫ R)).symm.trans
      (SSet.yonedaEquiv_symm_zero vθ)
  obtain ⟨W, _, hUnique⟩ := existsUnique_nativeCoverSimplexLiftFromFirst σθ vθ hvθ
  refine ⟨hvθ, ?_⟩
  exact (hUnique R ⟨hRp, hfirst⟩).trans
    ((hUnique (nativeCoverSimplexLiftFromFirstMap σθ vθ hvθ)
      ⟨nativeCoverSimplexLiftFromFirstMap_projection σθ vθ hvθ,
        nativeCoverSimplexLiftFromFirstMap_firstVertex σθ vθ hvθ⟩).symm)

end SSet.KanComplex

namespace SSet.KanComplex

/-- Naturality of the actual native fundamental-groupoid nerve unit. -/
theorem nativeCoverUnit_naturality
    {X Y : SSet.{u}} (i : X ⟶ Y) :
    i ≫ nativeCoverUnit Y =
      nativeCoverUnit X ≫ CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid i) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid i
  have hpre : SSet.fundamentalGroupoidNerveEquiv X (SSet.FundamentalGroupoid Y) F =
      i ≫ nativeCoverUnit Y := by
    simpa only [nativeCoverUnit, Functor.comp_id] using
      (SSet.fundamentalGroupoidNerveEquiv_precomp i (𝟭 (SSet.FundamentalGroupoid Y)))
  have hpost : SSet.fundamentalGroupoidNerveEquiv X (SSet.FundamentalGroupoid Y) F =
      nativeCoverUnit X ≫ CategoryTheory.nerveMap F := by
    simpa only [nativeCoverUnit, Functor.id_comp] using
      (SSet.fundamentalGroupoidNerveEquiv_postcomp
        (𝟭 (SSet.FundamentalGroupoid X)) F)
  exact hpre.symm.trans hpost

/-- Apply the actual fundamental-groupoid map to the original under-path nerve. -/
noncomputable def nativeCoverPathMap
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)) ⟶
      CategoryTheory.nerve
        (CategoryTheory.Under (SSet.FundamentalGroupoid.mk
          (i.app (Opposite.op ⦋0⦌) x))) :=
  CategoryTheory.nerveMap
    (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
      (SSet.mapFundamentalGroupoid i))

/-- The original path-nerve projections commute with the constructed map. -/
theorem nativeCoverPathMap_projection
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCoverPathMap i x ≫ nativeCoverNerveProjection Y (i.app (Opposite.op ⦋0⦌) x) =
      nativeCoverNerveProjection X x ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid i) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid i
  change CategoryTheory.nerveMap
      (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) F ⋙
        CategoryTheory.Under.forget (F.obj (SSet.FundamentalGroupoid.mk x))) =
    CategoryTheory.nerveMap
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk x) ⋙ F)
  exact congrArg (fun Q : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) ⥤
      SSet.FundamentalGroupoid Y => CategoryTheory.nerveMap Q)
    (CategoryTheory.Under.post_forget_eq_forget_comp F (SSet.FundamentalGroupoid.mk x))

private theorem nativeCoverMapSquare
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    (nativeCoverProjection X x ≫ i) ≫ nativeCoverUnit Y =
      (nativeCoverUnderProjection X x ≫ nativeCoverPathMap i x) ≫
        nativeCoverNerveProjection Y (i.app (Opposite.op ⦋0⦌) x) := by
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid i
  let q : CategoryTheory.nerve
      (CategoryTheory.Under (SSet.FundamentalGroupoid.mk
        (i.app (Opposite.op ⦋0⦌) x))) ⟶
      CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    nativeCoverNerveProjection Y (i.app (Opposite.op ⦋0⦌) x)
  have hcondition : nativeCoverProjection X x ≫ nativeCoverUnit X =
      nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x :=
    pullback.condition
  calc
    (nativeCoverProjection X x ≫ i) ≫ nativeCoverUnit Y =
        nativeCoverProjection X x ≫ (i ≫ nativeCoverUnit Y) := Category.assoc _ _ _
    _ = nativeCoverProjection X x ≫
        (nativeCoverUnit X ≫ CategoryTheory.nerveMap F) :=
      congrArg (fun a => nativeCoverProjection X x ≫ a) (nativeCoverUnit_naturality i)
    _ = (nativeCoverProjection X x ≫ nativeCoverUnit X) ≫
        CategoryTheory.nerveMap F := (Category.assoc _ _ _).symm
    _ = (nativeCoverUnderProjection X x ≫ nativeCoverNerveProjection X x) ≫
        CategoryTheory.nerveMap F :=
      congrArg (fun a => a ≫ CategoryTheory.nerveMap F) hcondition
    _ = nativeCoverUnderProjection X x ≫
        (nativeCoverNerveProjection X x ≫ CategoryTheory.nerveMap F) :=
      Category.assoc _ _ _
    _ = nativeCoverUnderProjection X x ≫ (nativeCoverPathMap i x ≫ q) :=
      congrArg (fun a => nativeCoverUnderProjection X x ≫ a)
        (nativeCoverPathMap_projection i x).symm
    _ = (nativeCoverUnderProjection X x ≫ nativeCoverPathMap i x) ≫ q :=
      (Category.assoc _ _ _).symm

/-- The actual induced map between the original native pullbacks. -/
noncomputable def nativeCoverMap
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCover X x ⟶ nativeCover Y (i.app (Opposite.op ⦋0⦌) x) :=
  pullback.lift (nativeCoverProjection X x ≫ i)
    (nativeCoverUnderProjection X x ≫ nativeCoverPathMap i x)
    (by exact nativeCoverMapSquare i x)

/-- The constructed map lies over the original simplicial map. -/
theorem nativeCoverMap_projection
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCoverMap i x ≫
        nativeCoverProjection Y (i.app (Opposite.op ⦋0⦌) x) =
      nativeCoverProjection X x ≫ i := by
  dsimp only [nativeCoverMap, nativeCoverProjection]
  exact pullback.lift_fst _ _ _

/-- The second projection is the actual induced original under-path map. -/
theorem nativeCoverMap_underProjection
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    nativeCoverMap i x ≫
        nativeCoverUnderProjection Y (i.app (Opposite.op ⦋0⦌) x) =
      nativeCoverUnderProjection X x ≫ nativeCoverPathMap i x := by
  dsimp only [nativeCoverMap, nativeCoverUnderProjection]
  exact pullback.lift_snd _ _ _

end SSet.KanComplex

namespace SSet.KanComplex

/-- The constructed basechange map sends the original identity point to the original image point. -/
theorem nativeCoverMap_identityPoint
    {X Y : SSet.{u}} (i : X ⟶ Y) (x : X _⦋0⦌) :
    (nativeCoverMap i x).app (Opposite.op ⦋0⦌) (nativeCoverIdentityPoint X x) =
      nativeCoverIdentityPoint Y (i.app (Opposite.op ⦋0⦌) x) := by
  let y : Y _⦋0⦌ := i.app (Opposite.op ⦋0⦌) x
  let P : SSet.{u} := nativeCover X x
  let Q : SSet.{u} := nativeCover Y y
  let A : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))
  let B : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk y))
  let p : P ⟶ X := nativeCoverProjection X x
  let q : Q ⟶ Y := nativeCoverProjection Y y
  let r : P ⟶ A := nativeCoverUnderProjection X x
  let t : Q ⟶ B := nativeCoverUnderProjection Y y
  let M : P ⟶ Q := nativeCoverMap i x
  let T : A ⟶ B := nativeCoverPathMap i x
  let b : P _⦋0⦌ := nativeCoverIdentityPoint X x
  let c : Q _⦋0⦌ := nativeCoverIdentityPoint Y y
  have hp : q.app (Opposite.op ⦋0⦌) (M.app (Opposite.op ⦋0⦌) b) = y :=
    (congrArg (fun f : P ⟶ Y => f.app (Opposite.op ⦋0⦌) b)
      (nativeCoverMap_projection i x)).trans
        (congrArg (fun v : X _⦋0⦌ => i.app (Opposite.op ⦋0⦌) v)
          (nativeCoverProjection_identityPoint X x))
  have hq : q.app (Opposite.op ⦋0⦌) c = y := nativeCoverProjection_identityPoint Y y
  let F : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Y :=
    SSet.mapFundamentalGroupoid i
  let U : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) :=
    CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk x))
  let V : CategoryTheory.Under (SSet.FundamentalGroupoid.mk y) :=
    CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk y))
  have hU : (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) F).obj U = V := by
    change CategoryTheory.Under.mk (F.map (𝟙 (SSet.FundamentalGroupoid.mk x))) =
      CategoryTheory.Under.mk (𝟙 (F.obj (SSet.FundamentalGroupoid.mk x)))
    exact congrArg (fun f : F.obj (SSet.FundamentalGroupoid.mk x) ⟶
        F.obj (SSet.FundamentalGroupoid.mk x) => CategoryTheory.Under.mk f)
      (F.map_id (SSet.FundamentalGroupoid.mk x))
  have hT : T.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ U) =
      ComposableArrows.mk₀ V := by
    dsimp only [T, nativeCoverPathMap]
    exact (CategoryTheory.nerveMap_app_mk₀
      (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) F) U).trans
        (congrArg (fun W : CategoryTheory.Under (SSet.FundamentalGroupoid.mk y) =>
          ComposableArrows.mk₀ W) hU)
  have hr : r.app (Opposite.op ⦋0⦌) b = ComposableArrows.mk₀ U :=
    nativeCoverUnderProjection_identityPoint X x
  have ht : t.app (Opposite.op ⦋0⦌) c = ComposableArrows.mk₀ V :=
    nativeCoverUnderProjection_identityPoint Y y
  have hrt : t.app (Opposite.op ⦋0⦌) (M.app (Opposite.op ⦋0⦌) b) =
      t.app (Opposite.op ⦋0⦌) c :=
    (congrArg (fun f : P ⟶ B => f.app (Opposite.op ⦋0⦌) b)
      (nativeCoverMap_underProjection i x)).trans
        ((congrArg (fun s : A _⦋0⦌ => T.app (Opposite.op ⦋0⦌) s) hr).trans
          (hT.trans ht.symm))
  let v : Q _⦋0⦌ := M.app (Opposite.op ⦋0⦌) b
  have hproj : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Q) ≫ q =
      (SSet.const c : (Δ[0] : SSet.{u}) ⟶ Q) ≫ q :=
    (SSet.const_comp v q).trans
      ((congrArg (fun z : Y _⦋0⦌ => (SSet.const z : (Δ[0] : SSet.{u}) ⟶ Y))
        (hp.trans hq.symm)).trans (SSet.const_comp c q).symm)
  have hpath : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Q) ≫ t =
      (SSet.const c : (Δ[0] : SSet.{u}) ⟶ Q) ≫ t :=
    (SSet.const_comp v t).trans
      ((congrArg (fun z : B _⦋0⦌ => (SSet.const z : (Δ[0] : SSet.{u}) ⟶ B))
        hrt).trans (SSet.const_comp c t).symm)
  have hmaps : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Q) =
      (SSet.const c : (Δ[0] : SSet.{u}) ⟶ Q) :=
    nativeCover_hom_ext (X := Y) (x := y) hproj hpath
  change v = c
  exact (SSet.yonedaEquiv_const v).symm.trans
    ((congrArg (SSet.yonedaEquiv (X := Q) (n := ⦋0⦌)) hmaps).trans
      (SSet.yonedaEquiv_const c))

end SSet.KanComplex

namespace SSet.KanComplex

/-- The original under-path map preserves the identity simplicial map. -/
theorem nativeCoverPathMap_id
    {X : SSet.{u}} (x : X _⦋0⦌) :
    nativeCoverPathMap (𝟙 X) x =
      𝟙 (CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk x))) := by
  let T : SSet.Truncated.{u} 2 := (SSet.truncation 2).obj X
  have ht : (SSet.truncation 2).map (𝟙 X) = 𝟙 T :=
    (SSet.truncation 2).map_id X
  have hF : SSet.mapFundamentalGroupoid (𝟙 X) =
      𝟭 (SSet.FundamentalGroupoid X) :=
    (congrArg (fun f : T ⟶ T => SSet.Truncated.mapFundamentalGroupoid f) ht).trans
      (SSet.Truncated.mapFundamentalGroupoid_id T)
  have hpost (A B : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid X)
      (h : A = B) :
      HEq (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) A)
        (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) B) := by
    cases h
    rfl
  have hU : CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
        (SSet.mapFundamentalGroupoid (𝟙 X)) =
      CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
        (𝟭 (SSet.FundamentalGroupoid X)) := eq_of_heq (hpost _ _ hF)
  exact (congrArg (fun Q : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) ⥤
      CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) => CategoryTheory.nerveMap Q)
    hU).trans (by rfl)

/-- The actual original under-path maps preserve composition. -/
theorem nativeCoverPathMap_comp
    {X Y Z : SSet.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) (x : X _⦋0⦌) :
    nativeCoverPathMap i x ≫ nativeCoverPathMap j (i.app (Opposite.op ⦋0⦌) x) =
      nativeCoverPathMap (i ≫ j) x := by
  let TX : SSet.Truncated.{u} 2 := (SSet.truncation 2).obj X
  let TZ : SSet.Truncated.{u} 2 := (SSet.truncation 2).obj Z
  have ht : (SSet.truncation 2).map (i ≫ j) =
      (SSet.truncation 2).map i ≫ (SSet.truncation 2).map j :=
    (SSet.truncation 2).map_comp i j
  have hF : SSet.mapFundamentalGroupoid (i ≫ j) =
      SSet.mapFundamentalGroupoid i ⋙ SSet.mapFundamentalGroupoid j :=
    (congrArg (fun f : TX ⟶ TZ => SSet.Truncated.mapFundamentalGroupoid f) ht).trans
      (SSet.Truncated.mapFundamentalGroupoid_comp
        ((SSet.truncation 2).map i) ((SSet.truncation 2).map j))
  have hpost (A B : SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid Z)
      (h : A = B) :
      HEq (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) A)
        (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x) B) := by
    cases h
    rfl
  have hU : CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
        (SSet.mapFundamentalGroupoid (i ≫ j)) =
      CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
        (SSet.mapFundamentalGroupoid i ⋙ SSet.mapFundamentalGroupoid j) :=
    eq_of_heq (hpost _ _ hF)
  have hn : nativeCoverPathMap (i ≫ j) x = CategoryTheory.nerveMap
      (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
        (SSet.mapFundamentalGroupoid i ⋙ SSet.mapFundamentalGroupoid j)) :=
    congrArg (fun Q : CategoryTheory.Under (SSet.FundamentalGroupoid.mk x) ⥤
      CategoryTheory.Under (SSet.FundamentalGroupoid.mk
        ((i ≫ j).app (Opposite.op ⦋0⦌) x)) => CategoryTheory.nerveMap Q) hU
  exact (show nativeCoverPathMap i x ≫
      nativeCoverPathMap j (i.app (Opposite.op ⦋0⦌) x) = CategoryTheory.nerveMap
        (CategoryTheory.Under.post (X := SSet.FundamentalGroupoid.mk x)
          (SSet.mapFundamentalGroupoid i ⋙ SSet.mapFundamentalGroupoid j)) from rfl).trans
    hn.symm

/-- The induced original cover map preserves the identity. -/
theorem nativeCoverMap_id
    {X : SSet.{u}} (x : X _⦋0⦌) :
    nativeCoverMap (𝟙 X) x = 𝟙 (nativeCover X x) := by
  apply nativeCover_hom_ext
  · exact (nativeCoverMap_projection (𝟙 X) x).trans
      ((Category.comp_id (nativeCoverProjection X x)).trans
        (Category.id_comp (nativeCoverProjection X x)).symm)
  · have h := nativeCoverMap_underProjection (𝟙 X) x
    exact h.trans
      ((congrArg (fun a => nativeCoverUnderProjection X x ≫ a)
        (nativeCoverPathMap_id x)).trans
          ((Category.comp_id (nativeCoverUnderProjection X x)).trans
            (Category.id_comp (nativeCoverUnderProjection X x)).symm))

/-- The constructed maps between the original pullbacks preserve composition. -/
theorem nativeCoverMap_comp
    {X Y Z : SSet.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) (x : X _⦋0⦌) :
    nativeCoverMap i x ≫ nativeCoverMap j (i.app (Opposite.op ⦋0⦌) x) =
      nativeCoverMap (i ≫ j) x := by
  let y : Y _⦋0⦌ := i.app (Opposite.op ⦋0⦌) x
  let z : Z _⦋0⦌ := j.app (Opposite.op ⦋0⦌) y
  apply nativeCover_hom_ext
  · calc
      (nativeCoverMap i x ≫ nativeCoverMap j y) ≫ nativeCoverProjection Z z =
          nativeCoverMap i x ≫ (nativeCoverMap j y ≫ nativeCoverProjection Z z) :=
        Category.assoc _ _ _
      _ = nativeCoverMap i x ≫ (nativeCoverProjection Y y ≫ j) :=
        congrArg (fun a => nativeCoverMap i x ≫ a) (nativeCoverMap_projection j y)
      _ = (nativeCoverMap i x ≫ nativeCoverProjection Y y) ≫ j :=
        (Category.assoc _ _ _).symm
      _ = (nativeCoverProjection X x ≫ i) ≫ j :=
        congrArg (fun a => a ≫ j) (nativeCoverMap_projection i x)
      _ = nativeCoverProjection X x ≫ (i ≫ j) := Category.assoc _ _ _
      _ = nativeCoverMap (i ≫ j) x ≫ nativeCoverProjection Z z :=
        (nativeCoverMap_projection (i ≫ j) x).symm
  · calc
      (nativeCoverMap i x ≫ nativeCoverMap j y) ≫ nativeCoverUnderProjection Z z =
          nativeCoverMap i x ≫ (nativeCoverMap j y ≫ nativeCoverUnderProjection Z z) :=
        Category.assoc _ _ _
      _ = nativeCoverMap i x ≫ (nativeCoverUnderProjection Y y ≫ nativeCoverPathMap j y) :=
        congrArg (fun a => nativeCoverMap i x ≫ a) (nativeCoverMap_underProjection j y)
      _ = (nativeCoverMap i x ≫ nativeCoverUnderProjection Y y) ≫ nativeCoverPathMap j y :=
        (Category.assoc _ _ _).symm
      _ = (nativeCoverUnderProjection X x ≫ nativeCoverPathMap i x) ≫
          nativeCoverPathMap j y :=
        congrArg (fun a => a ≫ nativeCoverPathMap j y) (nativeCoverMap_underProjection i x)
      _ = nativeCoverUnderProjection X x ≫ (nativeCoverPathMap i x ≫ nativeCoverPathMap j y) :=
        Category.assoc _ _ _
      _ = nativeCoverUnderProjection X x ≫ nativeCoverPathMap (i ≫ j) x :=
        congrArg (fun a => nativeCoverUnderProjection X x ≫ a) (nativeCoverPathMap_comp i j x)
      _ = nativeCoverMap (i ≫ j) x ≫ nativeCoverUnderProjection Z z :=
        (nativeCoverMap_underProjection (i ≫ j) x).symm

end SSet.KanComplex

end

public section

namespace SSet.KanComplex

/-- The existing vertex coordinate retains its actual original Under-nerve
vertex, without changing its endpoint or chosen path. -/
theorem nativeCoverVertexUnderEquiv_val {X : SSet.{u}} {x : X _⦋0⦌}
    (z : X _⦋0⦌)
    (v : {v : (nativeCover X x) _⦋0⦌ // (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    (nativeCoverVertexUnderEquiv z v).val =
      CategoryTheory.nerveEquiv
        ((nativeCoverUnderProjection X x).app (Opposite.op ⦋0⦌) v.val) := by
  rfl

/-- The SAME computed native base-change map applies the original
fundamental-groupoid map to every path coordinate, including arbitrary
first-path shifts. -/
theorem nativeCoverVertexPathEquiv_symm_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (x z : X _⦋0⦌) (g : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) :
    (nativeCoverMap f x).app (Opposite.op ⦋0⦌)
        ((nativeCoverVertexPathEquiv z).symm g).val =
      ((nativeCoverVertexPathEquiv (X := Y) (x := f.app (Opposite.op ⦋0⦌) x)
        (f.app (Opposite.op ⦋0⦌) z)).symm ((SSet.mapFundamentalGroupoid f).map g)).val := by
  let F := SSet.mapFundamentalGroupoid f
  let y := f.app (Opposite.op ⦋0⦌) x
  let w := f.app (Opposite.op ⦋0⦌) z
  let P := nativeCover X x
  let Q := nativeCover Y y
  let p := nativeCoverProjection Y y
  let rX := nativeCoverUnderProjection X x
  let rY := nativeCoverUnderProjection Y y
  let U := CategoryTheory.Under (SSet.FundamentalGroupoid.mk x)
  let V := CategoryTheory.Under (SSet.FundamentalGroupoid.mk y)
  let a : {v : P _⦋0⦌ // (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z} :=
    (nativeCoverVertexPathEquiv z).symm g
  let b : {v : Q _⦋0⦌ // p.app (Opposite.op ⦋0⦌) v = w} :=
    (nativeCoverVertexPathEquiv w).symm (F.map g)
  let v : Q _⦋0⦌ := (nativeCoverMap f x).app (Opposite.op ⦋0⦌) a.val
  have hA : CategoryTheory.nerveEquiv (rX.app (Opposite.op ⦋0⦌) a.val) = Under.mk g := by
    have h := congrArg Subtype.val
      ((nativeCoverVertexUnderEquiv z).apply_symm_apply
        (⟨Under.mk g,
            rfl⟩ : {U : Under (SSet.FundamentalGroupoid.mk x) // U.right =
            SSet.FundamentalGroupoid.mk z}))
    exact (nativeCoverVertexUnderEquiv_val z a).symm.trans h
  have hB : CategoryTheory.nerveEquiv (rY.app (Opposite.op ⦋0⦌) b.val) = Under.mk (F.map g) := by
    have h := congrArg Subtype.val
      ((nativeCoverVertexUnderEquiv w).apply_symm_apply
        (⟨Under.mk (F.map g),
            rfl⟩ : {U : Under (SSet.FundamentalGroupoid.mk y) // U.right =
            SSet.FundamentalGroupoid.mk w}))
    exact (nativeCoverVertexUnderEquiv_val w b).symm.trans h
  have hRaw : rX.app (Opposite.op ⦋0⦌) a.val =
      (CategoryTheory.nerveEquiv (C := U)).symm (Under.mk g) :=
    (CategoryTheory.nerveEquiv (C := U)).injective
      (hA.trans ((CategoryTheory.nerveEquiv (C := U)).apply_symm_apply _).symm)
  have hMap : rY.app (Opposite.op ⦋0⦌) v =
      (nativeCoverPathMap f x).app (Opposite.op ⦋0⦌)
        (rX.app (Opposite.op ⦋0⦌) a.val) :=
    congrArg (fun k => k.app (Opposite.op ⦋0⦌) a.val) (nativeCoverMap_underProjection f x)
  have hImage : CategoryTheory.nerveEquiv
      ((nativeCoverPathMap f x).app (Opposite.op ⦋0⦌)
        (rX.app (Opposite.op ⦋0⦌) a.val)) = Under.mk (F.map g) := by
    rw [hRaw]
    change CategoryTheory.nerveEquiv
      ((CategoryTheory.nerveMap (Under.post (X := SSet.FundamentalGroupoid.mk x) F)).app
        (Opposite.op ⦋0⦌) (CategoryTheory.ComposableArrows.mk₀ (Under.mk g))) = _
    rw [CategoryTheory.nerveMap_app_mk₀]
    rfl
  have hR : rY.app (Opposite.op ⦋0⦌) v = rY.app (Opposite.op ⦋0⦌) b.val :=
    (CategoryTheory.nerveEquiv (C := V)).injective
      ((congrArg (CategoryTheory.nerveEquiv (C := V)) hMap).trans (hImage.trans hB.symm))
  have hP : p.app (Opposite.op ⦋0⦌) v = p.app (Opposite.op ⦋0⦌) b.val :=
    ((congrArg (fun k => k.app (Opposite.op ⦋0⦌) a.val) (nativeCoverMap_projection f x)).trans
      (congrArg (f.app (Opposite.op ⦋0⦌)) a.property)).trans b.property.symm
  have hp : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Q) ≫ p =
      (SSet.const b.val : (Δ[0] : SSet.{u}) ⟶ Q) ≫ p :=
    (SSet.const_comp v p).trans
      ((congrArg (fun t => (SSet.const t : (Δ[0] : SSet.{u}) ⟶ Y)) hP).trans
        (SSet.const_comp b.val p).symm)
  have hr : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Q) ≫ rY =
      (SSet.const b.val : (Δ[0] : SSet.{u}) ⟶ Q) ≫ rY :=
    (SSet.const_comp v rY).trans
      ((congrArg (fun t => (SSet.const t : (Δ[0] : SSet.{u}) ⟶ CategoryTheory.nerve V)) hR).trans
        (SSet.const_comp b.val rY).symm)
  have hc : (SSet.const v : (Δ[0] : SSet.{u}) ⟶ Q) = SSet.const b.val :=
    nativeCover_hom_ext hp hr
  exact (SSet.yonedaEquiv_const v).symm.trans
    ((congrArg (SSet.yonedaEquiv (X := Q) (n := ⦋0⦌)) hc).trans (SSet.yonedaEquiv_const b.val))

/-- The forward path-coordinate equation for the same original native map. -/
theorem nativeCoverVertexPathEquiv_map {X Y : SSet.{u}} (f : X ⟶ Y) (x z : X _⦋0⦌)
    (v : {v : (nativeCover X x) _⦋0⦌ // (nativeCoverProjection X x).app (Opposite.op ⦋0⦌) v = z}) :
    nativeCoverVertexPathEquiv (f.app (Opposite.op ⦋0⦌) z)
      (⟨(nativeCoverMap f x).app (Opposite.op ⦋0⦌) v.val,
        (congrArg (fun k => k.app (Opposite.op ⦋0⦌) v.val) (nativeCoverMap_projection f x)).trans
          (congrArg (f.app (Opposite.op ⦋0⦌)) v.property)⟩ :
        {w : (nativeCover Y (f.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ //
          (nativeCoverProjection Y (f.app (Opposite.op ⦋0⦌) x)).app
            (Opposite.op ⦋0⦌) w = f.app (Opposite.op ⦋0⦌) z}) =
      (SSet.mapFundamentalGroupoid f).map (nativeCoverVertexPathEquiv z v) := by
  let g := nativeCoverVertexPathEquiv z v
  let E := nativeCoverVertexPathEquiv (X := Y) (x := f.app (Opposite.op ⦋0⦌) x)
    (f.app (Opposite.op ⦋0⦌) z)
  let w : {w : (nativeCover Y (f.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ //
      (nativeCoverProjection Y (f.app (Opposite.op ⦋0⦌) x)).app
        (Opposite.op ⦋0⦌) w = f.app (Opposite.op ⦋0⦌) z} :=
    ⟨(nativeCoverMap f x).app (Opposite.op ⦋0⦌) v.val,
      (congrArg (fun k => k.app (Opposite.op ⦋0⦌) v.val) (nativeCoverMap_projection f x)).trans
        (congrArg (f.app (Opposite.op ⦋0⦌)) v.property)⟩
  have hval : w.val = (E.symm ((SSet.mapFundamentalGroupoid f).map g)).val :=
    (congrArg (fun a => (nativeCoverMap f x).app (Opposite.op ⦋0⦌) a.val)
      ((nativeCoverVertexPathEquiv z).symm_apply_apply v)).symm.trans
        (nativeCoverVertexPathEquiv_symm_map f x z g)
  have hw : w = E.symm ((SSet.mapFundamentalGroupoid f).map g) := Subtype.ext hval
  exact (congrArg E hw).trans (E.apply_symm_apply _)

end SSet.KanComplex
