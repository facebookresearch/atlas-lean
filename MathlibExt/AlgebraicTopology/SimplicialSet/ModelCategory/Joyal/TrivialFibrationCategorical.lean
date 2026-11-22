/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract
public import MathlibExt.AlgebraicTopology.SimplicialSet.Slice
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-!
# Trivial Kan fibrations are Joyal categorical equivalences (the supporting results)

```text
SSet.modelCategoryQuillen.I.rlp ≤ SSet.categoricalEquivalences.
```

The edge dictionary for functor objects used downstream —
`SSet.Homotopy.edgeIhom`, currying a homotopy `K : SSet.Homotopy f g`
with `f g : X ⟶ C` to an edge of `(ihom X).obj C` between the vertices
classified by `f` and `g` — is generic simplicial-set infrastructure of
the neutral module
`MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom`, which this
file public-imports (re-exports). These edges are the components of
the natural transformation assembled in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}} {p : X ⟶ Y}

/-!
## The cylinder boundary as a binary coproduct

`X ⊗ ∂Δ[1]` is the coproduct of two copies of `X ⊗ Δ[0]` along the two
face inclusions `boundary.ι i : Δ[0] ⟶ ∂Δ[1]`, since `∂Δ[1]` is the
coproduct of its two vertices (a bicartesian square of subcomplexes of
`Δ[1]`, as in `SSet.pathSpace` for the other tensor order) and
`tensorLeft X` preserves colimits. This gives the desc used to assemble
the top map of the lifting square from its two ends.
-/

private lemma tfcBoundaryOneBicart :
    Subcomplex.BicartSq (⊥ : (Δ[1] : SSet.{u}).Subcomplex)
      (stdSimplex.face ({1}ᶜ : Finset (Fin 2)))
      (stdSimplex.face ({0}ᶜ : Finset (Fin 2))) (boundary 1) := by
  constructor
  · calc
      stdSimplex.face (({1}ᶜ : Finset (Fin 2))) ⊔
          stdSimplex.face (({0}ᶜ : Finset (Fin 2))) =
        stdSimplex.face (({0}ᶜ : Finset (Fin 2))) ⊔
          stdSimplex.face (({1}ᶜ : Finset (Fin 2))) := sup_comm _ _
      _ = ⨆ i : Fin 2, stdSimplex.face (({i}ᶜ : Finset (Fin 2))) := by
        apply le_antisymm
        · exact sup_le
            (le_iSup (f := fun i : Fin 2 =>
              stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 0)
            (le_iSup (f := fun i : Fin 2 =>
              stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 1)
        · apply iSup_le
          intro i
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right
      _ = boundary 1 := (boundary_eq_iSup (n := 1)).symm
  · rw [stdSimplex.face_inter_face]
    have h : (({1}ᶜ : Finset (Fin 2)) ⊓ {0}ᶜ : Finset (Fin 2)) = ∅ := by decide
    rw [h]
    exact stdSimplex.face_empty 1

private noncomputable def tfcBoundaryOneCofanIsColimit :
    IsColimit (BinaryCofan.mk (boundary.ι (1 : Fin 2)) (boundary.ι (0 : Fin 2))) := by
  have hPush := tfcBoundaryOneBicart.{u}.isPushout
  have hPush' : IsPushout
      ((Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).to (Δ[0] : SSet.{u}))
      ((Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).to (Δ[0] : SSet.{u}))
      (boundary.ι (1 : Fin 2)) (boundary.ι (0 : Fin 2)) := by
    fapply hPush.of_iso' (Iso.refl (((⊥ : (Δ[1] : SSet.{u}).Subcomplex) : SSet)))
      (stdSimplex.faceSingletonComplIso (1 : Fin 2))
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)) (Iso.refl _)
    · apply (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).hom_ext
    · apply (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).hom_ext
    · change (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫
          boundary.faceι 1 = boundary.ι 1
      rw [← boundary.faceSingletonComplIso_inv_ι, Iso.hom_inv_id_assoc]
    · change (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom ≫
          boundary.faceι 0 = boundary.ι 0
      rw [← boundary.faceSingletonComplIso_inv_ι, Iso.hom_inv_id_assoc]
  exact isCoproductOfIsInitialIsPushout _ _ _ _
    (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))) hPush'.isColimit

private noncomputable def tfcBoundaryOneTensorLeftCofanIsColimit (X : SSet.{u}) :
    IsColimit (BinaryCofan.mk (X ◁ boundary.ι (1 : Fin 2))
      (X ◁ boundary.ι (0 : Fin 2))) :=
  mapIsColimitOfPreservesOfIsColimit (tensorLeft X) _ _ tfcBoundaryOneCofanIsColimit

/-- The canonical isomorphism `X ⊗ Δ[0] ≅ X`, from
`SSet.Δ0IsoUnit : Δ[0] ≅ 𝟙_ SSet` and the right unitor. -/
private noncomputable def tensorDeltaZeroIso (X : SSet.{u}) :
    X ⊗ (Δ[0] : SSet.{u}) ≅ X :=
  whiskerLeftIso X Δ0IsoUnit ≪≫ ρ_ X

/-- Assembly of a map out of the cylinder boundary `X ⊗ ∂Δ[1]` from its
two ends `a` (at vertex `0`) and `b` (at vertex `1`). -/
private noncomputable def cylBoundaryDesc {Z : SSet.{u}} (a b : X ⟶ Z) :
    X ⊗ (∂Δ[1] : SSet.{u}) ⟶ Z :=
  BinaryCofan.IsColimit.desc (tfcBoundaryOneTensorLeftCofanIsColimit X)
    ((tensorDeltaZeroIso X).hom ≫ a) ((tensorDeltaZeroIso X).hom ≫ b)

@[reassoc (attr := simp)]
private lemma whiskerLeft_boundary_ι_one_cylBoundaryDesc {Z : SSet.{u}}
    (a b : X ⟶ Z) :
    (X ◁ boundary.ι (1 : Fin 2)) ≫ cylBoundaryDesc a b =
      (tensorDeltaZeroIso X).hom ≫ a :=
  BinaryCofan.IsColimit.inl_desc (tfcBoundaryOneTensorLeftCofanIsColimit X) _ _

@[reassoc (attr := simp)]
private lemma whiskerLeft_boundary_ι_zero_cylBoundaryDesc {Z : SSet.{u}}
    (a b : X ⟶ Z) :
    (X ◁ boundary.ι (0 : Fin 2)) ≫ cylBoundaryDesc a b =
      (tensorDeltaZeroIso X).hom ≫ b :=
  BinaryCofan.IsColimit.inr_desc (tfcBoundaryOneTensorLeftCofanIsColimit X) _ _

@[reassoc]
private lemma tensorDeltaZeroIso_inv_boundary_ι_one_cylBoundaryDesc
    {Z : SSet.{u}} (a b : X ⟶ Z) :
    (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (1 : Fin 2)) ≫
        cylBoundaryDesc a b = a := by
  rw [whiskerLeft_boundary_ι_one_cylBoundaryDesc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

@[reassoc]
private lemma tensorDeltaZeroIso_inv_boundary_ι_zero_cylBoundaryDesc
    {Z : SSet.{u}} (a b : X ⟶ Z) :
    (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (0 : Fin 2)) ≫
        cylBoundaryDesc a b = b := by
  rw [whiskerLeft_boundary_ι_zero_cylBoundaryDesc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Two maps out of `X ⊗ ∂Δ[1]` agreeing on both ends are equal. -/
private lemma cylBoundary_hom_ext {Z : SSet.{u}}
    {u v : X ⊗ (∂Δ[1] : SSet.{u}) ⟶ Z}
    (h₁ : (X ◁ boundary.ι (1 : Fin 2)) ≫ u = (X ◁ boundary.ι (1 : Fin 2)) ≫ v)
    (h₀ : (X ◁ boundary.ι (0 : Fin 2)) ≫ u = (X ◁ boundary.ι (0 : Fin 2)) ≫ v) :
    u = v :=
  BinaryCofan.IsColimit.hom_ext (tfcBoundaryOneTensorLeftCofanIsColimit X) h₁ h₀

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `0` is the Yoneda name of
that vertex. -/
private lemma stdSimplex_δ_one_eq_yonedaEquiv_symm :
    stdSimplex.δ (1 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm 0) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (1 : Fin 2) = stdSimplex.δ (1 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from
    (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `1` is the Yoneda name of
that vertex. -/
private lemma stdSimplex_δ_zero_eq_yonedaEquiv_symm :
    stdSimplex.δ (0 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm 1) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (0 : Fin 2) = stdSimplex.δ (0 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from
    (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

/-- The second projection after `(tensorDeltaZeroIso X).inv`, followed by
a face inclusion `Δ[0] ⟶ Δ[1]`, is the constant map at the corresponding
vertex: any map `X ⟶ Δ[0]` is constant since `Δ[0]` has a unique simplex
in each degree. -/
private lemma tensorDeltaZeroIso_inv_snd_comp_δ (i : Fin 2) (c : Fin 2)
    (hc : ∀ v : (Δ[0] : SSet.{u}) _⦋0⦌,
      (stdSimplex.δ i).app (op ⦋0⦌) v = stdSimplex.obj₀Equiv.{u}.symm c) :
    (tensorDeltaZeroIso X).inv ≫ snd X (Δ[0] : SSet.{u}) ≫ stdSimplex.δ i =
      const (stdSimplex.obj₀Equiv.{u}.symm c) := by
  have hconst : (tensorDeltaZeroIso X).inv ≫ snd X (Δ[0] : SSet.{u}) =
      const ((stdSimplex.obj₀Equiv (n := 0)).symm 0) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← Category.assoc, hconst, const_comp, hc]

private lemma δ_one_app_zero (v : (Δ[0] : SSet.{u}) _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 2)).app (op ⦋0⦌) v =
      stdSimplex.obj₀Equiv.{u}.symm 0 := by
  have h1 : yonedaEquiv.symm v = 𝟙 (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  calc (stdSimplex.δ (1 : Fin 2)).app (op ⦋0⦌) v
      = yonedaEquiv (yonedaEquiv.symm ((stdSimplex.δ (1 : Fin 2)).app (op ⦋0⦌) v)) :=
        (Equiv.apply_symm_apply _ _).symm
    _ = yonedaEquiv (yonedaEquiv.symm v ≫ stdSimplex.δ (1 : Fin 2)) := by
        rw [yonedaEquiv_symm_comp]
    _ = yonedaEquiv (stdSimplex.δ (1 : Fin 2)) := by rw [h1, Category.id_comp]
    _ = stdSimplex.obj₀Equiv.{u}.symm 0 := by
        rw [stdSimplex_δ_one_eq_yonedaEquiv_symm, Equiv.apply_symm_apply]

private lemma δ_zero_app_zero (v : (Δ[0] : SSet.{u}) _⦋0⦌) :
    (stdSimplex.δ (0 : Fin 2)).app (op ⦋0⦌) v =
      stdSimplex.obj₀Equiv.{u}.symm 1 := by
  have h1 : yonedaEquiv.symm v = 𝟙 (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  calc (stdSimplex.δ (0 : Fin 2)).app (op ⦋0⦌) v
      = yonedaEquiv (yonedaEquiv.symm ((stdSimplex.δ (0 : Fin 2)).app (op ⦋0⦌) v)) :=
        (Equiv.apply_symm_apply _ _).symm
    _ = yonedaEquiv (yonedaEquiv.symm v ≫ stdSimplex.δ (0 : Fin 2)) := by
        rw [yonedaEquiv_symm_comp]
    _ = yonedaEquiv (stdSimplex.δ (0 : Fin 2)) := by rw [h1, Category.id_comp]
    _ = stdSimplex.obj₀Equiv.{u}.symm 1 := by
        rw [stdSimplex_δ_zero_eq_yonedaEquiv_symm, Equiv.apply_symm_apply]

/-- The `0`-end cylinder inclusion `SSet.ι₀` factors through the cylinder
boundary via the vertex-`0` leg of the coproduct. -/
private lemma ι₀_eq :
    (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (1 : Fin 2)) ≫
        (X ◁ (boundary 1).ι) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [SSet.ι₀_fst]
    calc (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (1 : Fin 2)) ≫
          (X ◁ (boundary 1).ι) ≫ fst X (Δ[1] : SSet.{u})
        = (tensorDeltaZeroIso X).inv ≫ fst X (Δ[0] : SSet.{u}) := by
          rw [CartesianMonoidalCategory.whiskerLeft_fst,
            CartesianMonoidalCategory.whiskerLeft_fst]
      _ = (ρ_ X).inv ≫ (X ◁ Δ0IsoUnit.inv) ≫ fst X (Δ[0] : SSet.{u}) := rfl
      _ = 𝟙 X := by
          rw [CartesianMonoidalCategory.whiskerLeft_fst]
          exact CartesianMonoidalCategory.rightUnitor_inv_fst X
  · rw [SSet.ι₀_snd]
    calc (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (1 : Fin 2)) ≫
          (X ◁ (boundary 1).ι) ≫ snd X (Δ[1] : SSet.{u})
        = (tensorDeltaZeroIso X).inv ≫ snd X (Δ[0] : SSet.{u}) ≫
            (boundary.ι (1 : Fin 2) ≫ (boundary 1).ι) := by
          simp [CartesianMonoidalCategory.whiskerLeft_snd]
      _ = (tensorDeltaZeroIso X).inv ≫ snd X (Δ[0] : SSet.{u}) ≫
            stdSimplex.δ (1 : Fin 2) := by rw [boundary.ι_ι]
      _ = const (stdSimplex.obj₀Equiv.{u}.symm 0) :=
          tensorDeltaZeroIso_inv_snd_comp_δ 1 0 (fun v => δ_one_app_zero v)

/-- The `1`-end cylinder inclusion `SSet.ι₁` factors through the cylinder
boundary via the vertex-`1` leg of the coproduct. -/
private lemma ι₁_eq :
    (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (0 : Fin 2)) ≫
        (X ◁ (boundary 1).ι) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [SSet.ι₁_fst]
    calc (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (0 : Fin 2)) ≫
          (X ◁ (boundary 1).ι) ≫ fst X (Δ[1] : SSet.{u})
        = (tensorDeltaZeroIso X).inv ≫ fst X (Δ[0] : SSet.{u}) := by
          rw [CartesianMonoidalCategory.whiskerLeft_fst,
            CartesianMonoidalCategory.whiskerLeft_fst]
      _ = (ρ_ X).inv ≫ (X ◁ Δ0IsoUnit.inv) ≫ fst X (Δ[0] : SSet.{u}) := rfl
      _ = 𝟙 X := by
          rw [CartesianMonoidalCategory.whiskerLeft_fst]
          exact CartesianMonoidalCategory.rightUnitor_inv_fst X
  · rw [SSet.ι₁_snd]
    calc (tensorDeltaZeroIso X).inv ≫ (X ◁ boundary.ι (0 : Fin 2)) ≫
          (X ◁ (boundary 1).ι) ≫ snd X (Δ[1] : SSet.{u})
        = (tensorDeltaZeroIso X).inv ≫ snd X (Δ[0] : SSet.{u}) ≫
            (boundary.ι (0 : Fin 2) ≫ (boundary 1).ι) := by
          simp [CartesianMonoidalCategory.whiskerLeft_snd]
      _ = (tensorDeltaZeroIso X).inv ≫ snd X (Δ[0] : SSet.{u}) ≫
            stdSimplex.δ (0 : Fin 2) := by rw [boundary.ι_ι]
      _ = const (stdSimplex.obj₀Equiv.{u}.symm 1) :=
          tensorDeltaZeroIso_inv_snd_comp_δ 0 1 (fun v => δ_zero_app_zero v)

/-- The cylinder boundary inclusion is a monomorphism: it is, up to the
product-subcomplex isomorphism, the inclusion of the subcomplex
`⊤.prod (boundary 1)` of `X ⊗ Δ[1]`. -/
private lemma mono_whiskerLeft_boundary_one_ι :
    Mono (X ◁ (boundary 1).ι) := by
  let e := (Subcomplex.prodIso (⊤ : X.Subcomplex) (boundary 1)) ≪≫
    whiskerRightIso (Subcomplex.topIso X) ((boundary 1 : SSet.{u}) : SSet.{u})
  have hfac : e.hom ≫ (X ◁ (boundary 1).ι) =
      ((⊤ : X.Subcomplex).prod (boundary 1)).ι := rfl
  have hEq : X ◁ (boundary 1).ι =
      e.inv ≫ ((⊤ : X.Subcomplex).prod (boundary 1)).ι := by
    rw [← hfac, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hEq]
  infer_instance

/-- The forward map of `tensorDeltaZeroIso` is the first projection. -/
private lemma tensorDeltaZeroIso_hom :
    (tensorDeltaZeroIso X).hom = fst X (Δ[0] : SSet.{u}) := by
  change (X ◁ Δ0IsoUnit.hom) ≫ (ρ_ X).hom = fst X (Δ[0] : SSet.{u})
  rw [CartesianMonoidalCategory.rightUnitor_hom,
    CartesianMonoidalCategory.whiskerLeft_fst]

/-- Restricting the constant homotopy `fst ≫ q` to an end of the cylinder
boundary is the first projection followed by `q`. -/
private lemma whiskerLeft_boundary_ι_fst (i : Fin 2) {Z : SSet.{u}}
    (q : X ⟶ Z) :
    (X ◁ boundary.ι i) ≫ ((X ◁ (boundary 1).ι) ≫
      (fst X (Δ[1] : SSet.{u}) ≫ q)) = fst X (Δ[0] : SSet.{u}) ≫ q := by
  rw [← Category.assoc (X ◁ boundary.ι i), ← MonoidalCategory.whiskerLeft_comp,
    boundary.ι_ι, ← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]

/-!
## The coherent cylinder homotopy over a trivial Kan fibration
-/

/-- **Coherent cylinder homotopy over a trivial Kan fibration.** If `p` is
a trivial Kan fibration and `a b : X ⟶ X` become equal after composition
with `p`, then `a` and `b` are simplicially homotopic by a homotopy lying
over the constant homotopy of `a ≫ p` in `Y`: there is
`H : SSet.Homotopy a b` with
`H.h ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ (a ≫ p)`.

The proof is a single lift of `p` against the monomorphism
`X ◁ (boundary 1).ι : X ⊗ ∂Δ[1] ⟶ X ⊗ Δ[1]`
(`SSet.rlp_monomorphisms_of_rlp_I`), in the square whose top map
`X ⊗ ∂Δ[1] ⟶ X` is assembled from `a` and `b` on the two ends of the
cylinder and whose bottom map is `fst ≫ (a ≫ p)`; the square commutes
since `a ≫ p = b ≫ p`. This is the construction identified as the missing
input in the header of
`MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration`. -/
theorem exists_homotopy_over_of_rlp_I (hp : modelCategoryQuillen.I.rlp p)
    {a b : X ⟶ X} (hab : a ≫ p = b ≫ p) :
    ∃ H : Homotopy a b, H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p) := by
  have hpMono := rlp_monomorphisms_of_rlp_I hp
  have : Mono (X ◁ (boundary 1).ι) := mono_whiskerLeft_boundary_one_ι
  have : HasLiftingProperty (X ◁ (boundary 1).ι) p :=
    hpMono _ (MorphismProperty.monomorphisms.infer_property _)
  have hw : cylBoundaryDesc a b ≫ p =
      (X ◁ (boundary 1).ι) ≫ (fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p)) := by
    apply cylBoundary_hom_ext
    · calc (X ◁ boundary.ι (1 : Fin 2)) ≫ (cylBoundaryDesc a b ≫ p)
          = fst X (Δ[0] : SSet.{u}) ≫ (a ≫ p) := by
            rw [← Category.assoc, whiskerLeft_boundary_ι_one_cylBoundaryDesc,
              tensorDeltaZeroIso_hom, Category.assoc]
        _ = (X ◁ boundary.ι (1 : Fin 2)) ≫ ((X ◁ (boundary 1).ι) ≫
              (fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))) :=
            (whiskerLeft_boundary_ι_fst 1 (a ≫ p)).symm
    · calc (X ◁ boundary.ι (0 : Fin 2)) ≫ (cylBoundaryDesc a b ≫ p)
          = fst X (Δ[0] : SSet.{u}) ≫ (b ≫ p) := by
            rw [← Category.assoc, whiskerLeft_boundary_ι_zero_cylBoundaryDesc,
              tensorDeltaZeroIso_hom, Category.assoc]
        _ = fst X (Δ[0] : SSet.{u}) ≫ (a ≫ p) := by rw [hab]
        _ = (X ◁ boundary.ι (0 : Fin 2)) ≫ ((X ◁ (boundary 1).ι) ≫
              (fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))) :=
            (whiskerLeft_boundary_ι_fst 0 (a ≫ p)).symm
  let sq : CommSq (cylBoundaryDesc a b) (X ◁ (boundary 1).ι) p
      (fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p)) := ⟨hw⟩
  have h₀ : SSet.ι₀ ≫ sq.lift = a := by
    rw [ι₀_eq]
    simp only [Category.assoc]
    rw [sq.fac_left]
    exact tensorDeltaZeroIso_inv_boundary_ι_one_cylBoundaryDesc a b
  have h₁ : SSet.ι₁ ≫ sq.lift = b := by
    rw [ι₁_eq]
    simp only [Category.assoc]
    rw [sq.fac_left]
    exact tensorDeltaZeroIso_inv_boundary_ι_zero_cylBoundaryDesc a b
  let Hrel : HomotopyRel a b ⊥ :=
    ⟨sq.lift, h₀, h₁, by
      intro n x hx t
      cases hx⟩
  exact ⟨Hrel.toHomotopy, sq.fac_right⟩

/-- **Section and coherent homotopies for a trivial Kan fibration.** A
trivial Kan fibration `p : X ⟶ Y` admits a strict section `s : Y ⟶ X`
(`SSet.exists_section_of_rlp_I`) together with simplicial homotopies over
`p`, in both directions, between `𝟙 X` and `p ≫ s`: the homotopies `H`
satisfy `H.h ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p`, i.e. they
lie over the constant homotopy of `p` in `Y`. The homotopies are the
coherent cylinder homotopies of `SSet.exists_homotopy_over_of_rlp_I`,
applied to `(p ≫ s) ≫ p = p`. -/
theorem exists_section_and_homotopies_of_rlp_I
    (hp : modelCategoryQuillen.I.rlp p) :
    ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y ∧
      (∃ H : Homotopy (𝟙 X) (p ≫ s), H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ p) ∧
      (∃ H : Homotopy (p ≫ s) (𝟙 X), H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ p) := by
  obtain ⟨s, hs⟩ := exists_section_of_rlp_I hp
  have he : (p ≫ s) ≫ p = p := by
    rw [Category.assoc, hs, Category.comp_id]
  obtain ⟨H₁, hH₁⟩ := exists_homotopy_over_of_rlp_I hp
    (a := 𝟙 X) (b := p ≫ s) (by rw [Category.id_comp, he])
  obtain ⟨H₂, hH₂⟩ := exists_homotopy_over_of_rlp_I hp
    (a := p ≫ s) (b := 𝟙 X) (by rw [Category.id_comp, he])
  exact ⟨s, hs, ⟨H₁, by rwa [Category.id_comp] at hH₁⟩,
    ⟨H₂, by rwa [he] at hH₂⟩⟩

/-!
## The formal assembly step
-/

/-- **Assembly: a section plus a homotopy-category-level inverse gives a
categorical equivalence.** If `p : X ⟶ Y` has a section `s` and, for every
quasicategory `C`, precomposition with `p ≫ s` is naturally isomorphic to
the identity functor on `h Fun(X, C)`, then `p` is a categorical
equivalence: the functors `h Fun(p, C)` and `h Fun(s, C)` are mutually
inverse equivalences, the composite at `Y` being strictly the identity by
`s ≫ p = 𝟙 Y`, `SSet.hoFunctor_pre_comp`, and `SSet.hoFunctor_pre_id`.
Combined with `SSet.exists_section_and_homotopies_of_rlp_I`, this reduces
the target of the supporting results to exhibiting the displayed natural isomorphism
from a simplicial homotopy; that step (the additional comparison obligation in the
module header) is formalized in `HoPreNatIso.lean` as
`SSet.hoPreNatIso_of_homotopy_over_of_rlp_I`, which there completes
`SSet.categoricalEquivalences.of_rlp_I`. -/
theorem categoricalEquivalences.of_section_of_hoPre_id_natIso {s : Y ⟶ X}
    (hs : s ≫ p = 𝟙 Y)
    (H : ∀ (C : SSet.{u}), Quasicategory C →
      Nonempty (𝟭 (hoFunctor.obj ((ihom X).obj C)) ≅
        (hoFunctor.map ((pre (p ≫ s)).app C)).toFunctor)) :
    categoricalEquivalences p := by
  intro C hC
  obtain ⟨e⟩ := H C hC
  have e1 : (𝟭 (hoFunctor.obj ((ihom Y).obj C))) =
      (hoFunctor.map ((pre p).app C)).toFunctor ⋙
        (hoFunctor.map ((pre s).app C)).toFunctor := by
    rw [← hoFunctor_pre_comp, hs, hoFunctor_pre_id]
  exact Functor.IsEquivalence.mk' _ (eqToIso e1)
    ((eqToIso (hoFunctor_pre_comp C p s)).symm ≪≫ e.symm)

end SSet
