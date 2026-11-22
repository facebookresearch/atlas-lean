/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Finite products of the actual sequential group colimits

The product diagram uses the original coordinate group maps at the same
natural-number stage. Its comparison sends every whole quotient class to
its original coordinate classes. Finitely many representatives and their
equalities can be synchronized at one later original stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace GrpCat.FilteredColimits.FiniteProducts

variable {ι : Type} (F : ι → ℕ ⥤ GrpCat.{u})

/-- The original group family is multiplied at each same original natural-number stage. -/
def diagram : ℕ ⥤ GrpCat.{u} where
  obj n := GrpCat.of (∀ i, (F i).obj n)
  map f := GrpCat.ofHom {
    toFun := fun x i => ((F i).map f).hom (x i)
    map_one' := by funext i; exact map_one _
    map_mul' := by intro x y; funext i; exact map_mul _ _ _ }
  map_id n := by
    ext x i
    exact ConcreteCategory.congr_hom ((F i).map_id n) (x i)
  map_comp f g := by
    ext x i
    exact ConcreteCategory.congr_hom ((F i).map_comp f g) (x i)

/-- Each original coordinate projection is a whole natural transformation of group diagrams. -/
def projection (i : ι) : diagram F ⟶ F i where
  app _ := GrpCat.ofHom {
    toFun := fun x => x i
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- The original quotient comparison keeps the native colimit map of every full projection. -/
def comparison : colimit (diagram F) ⟶ GrpCat.of (∀ i, colimit (F i)) :=
  GrpCat.ofHom {
    toFun := fun x i => (colimitMap (projection F i)).hom x
    map_one' := by funext i; exact map_one _
    map_mul' := by intro x y; funext i; exact map_mul _ _ _ }

/-- Every original quotient representative retains its entire family of coordinate representatives. -/
theorem comparison_mk (n : ℕ) (x : (diagram F).obj n) (i : ι) :
    (comparison F).hom (G.mk (diagram F) ⟨n, x⟩) i = G.mk (F i) ⟨n, x i⟩ := by
  exact colimitMap_mk (projection F i) n x

/-- A whole original family of diagram maps acts coordinatewise on the same product diagram. -/
def map {F E : ι → ℕ ⥤ GrpCat.{u}} (a : ∀ i, F i ⟶ E i) : diagram F ⟶ diagram E where
  app n := GrpCat.ofHom {
    toFun := fun x i => (a i).app n |>.hom <| x i
    map_one' := by funext i; exact map_one _
    map_mul' := by intro x y; funext i; exact map_mul _ _ _ }
  naturality n m f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom ((a i).naturality f) (x i)

/-- The actual finite family of quotient maps retains each original full colimit map. -/
def quotientMap {F E : ι → ℕ ⥤ GrpCat.{u}} (a : ∀ i, F i ⟶ E i) :
    GrpCat.of (∀ i, colimit (F i)) ⟶ GrpCat.of (∀ i, colimit (E i)) :=
  GrpCat.ofHom {
    toFun := fun x i => (colimitMap (a i)).hom (x i)
    map_one' := by funext i; exact map_one _
    map_mul' := by intro x y; funext i; exact map_mul _ _ _ }

/-- Every whole original family of diagram maps commutes with the full quotient comparison. -/
theorem comparison_naturality {F E : ι → ℕ ⥤ GrpCat.{u}} (a : ∀ i, F i ⟶ E i) :
    colimitMap (map a) ≫ comparison E = comparison F ≫ quotientMap a := by
  apply (colimitCoconeIsColimit (diagram F)).hom_ext
  intro n
  ext x i
  change (comparison E).hom ((colimitMap (map a)).hom (G.mk (diagram F) ⟨n, x⟩)) i =
    (colimitMap (a i)).hom ((comparison F).hom (G.mk (diagram F) ⟨n, x⟩) i)
  rw [colimitMap_mk, comparison_mk, comparison_mk, colimitMap_mk]
  rfl

private theorem mk_map {D : ℕ ⥤ GrpCat.{u}} {n m : ℕ} (f : n ⟶ m) (x : D.obj n) :
    G.mk D ⟨m, (D.map f).hom x⟩ = G.mk D ⟨n, x⟩ :=
  G.mk_eq D _ _ ⟨m, 𝟙 m, f, by simp⟩

private theorem mk_eq_iff {D : ℕ ⥤ GrpCat.{u}}
    {n m : ℕ} (x : D.obj n) (y : D.obj m) :
    G.mk D ⟨n, x⟩ = G.mk D ⟨m, y⟩ ↔
      ∃ (k : ℕ) (f : n ⟶ k) (g : m ⟶ k), (D.map f).hom x = (D.map g).hom y := by
  change (D ⋙ forget GrpCat).ιColimitType n x =
    (D ⋙ forget GrpCat).ιColimitType m y ↔ _
  rw [Functor.ιColimitType_eq_iff,
    ← Types.FilteredColimit.rel_eq_eqvGen_colimitTypeRel]
  rfl

variable [Fintype ι]

/-- Every original finite family of quotient classes has a representative at one common stage. -/
theorem comparison_surjective : Function.Surjective (comparison F).hom := by
  intro y
  choose n x hx using fun i =>
    (F i ⋙ forget GrpCat).ιColimitType_jointly_surjective (y i)
  let N : ℕ := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let z : (diagram F).obj N := fun i => ((F i).map (homOfLE (hn i))).hom (x i)
  refine ⟨G.mk (diagram F) ⟨N, z⟩, ?_⟩
  funext i
  exact (comparison_mk F N z i).trans
    ((mk_map (homOfLE (hn i)) (x i)).trans (hx i))

/-- Equality of the whole coordinate class family is detected at one later original stage. -/
theorem comparison_injective : Function.Injective (comparison F).hom := by
  intro x y h
  obtain ⟨n, a, rfl⟩ := (diagram F ⋙ forget GrpCat).ιColimitType_jointly_surjective x
  obtain ⟨m, b, rfl⟩ := (diagram F ⋙ forget GrpCat).ιColimitType_jointly_surjective y
  have hi (i : ι) : G.mk (F i) ⟨n, a i⟩ = G.mk (F i) ⟨m, b i⟩ :=
    (comparison_mk F n a i).symm.trans ((congrFun h i).trans (comparison_mk F m b i))
  choose k f g hk using fun i => (mk_eq_iff (a i) (b i)).mp (hi i)
  let N : ℕ := max (max n m) (Finset.univ.sup k)
  have hn : n ≤ N := (Nat.le_max_left n m).trans (Nat.le_max_left _ _)
  have hm : m ≤ N := (Nat.le_max_right n m).trans (Nat.le_max_left _ _)
  have hki (i : ι) : k i ≤ N :=
    (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
  change G.mk (diagram F) ⟨n, a⟩ = G.mk (diagram F) ⟨m, b⟩
  apply G.mk_eq (diagram F)
  refine ⟨N, homOfLE hn, homOfLE hm, ?_⟩
  funext i
  change ((F i).map (homOfLE hn)).hom (a i) = ((F i).map (homOfLE hm)).hom (b i)
  have hf : f i ≫ homOfLE (hki i) = homOfLE hn := Subsingleton.elim _ _
  have hg : g i ≫ homOfLE (hki i) = homOfLE hm := Subsingleton.elim _ _
  have hmap := congrArg (((F i).map (homOfLE (hki i))).hom) (hk i)
  simpa only [← GrpCat.comp_apply, ← (F i).map_comp, hf, hg] using hmap

/-- The entire original finite-product comparison is genuinely an isomorphism of the native colimits. -/
def comparisonIso : colimit (diagram F) ≅ GrpCat.of (∀ i, colimit (F i)) :=
  (MulEquiv.ofBijective (comparison F).hom ⟨comparison_injective F, comparison_surjective F⟩).toGrpIso

/-- Its forward map is exactly the original full quotient comparison, with no change of representatives. -/
theorem comparisonIso_hom : (comparisonIso F).hom = comparison F := rfl

/-- Each coordinate projection of the full quotient Iso is its original colimit map. -/
theorem comparisonIso_coordinate (x : colimit (diagram F)) (i : ι) :
    (comparisonIso F).hom.hom x i = (colimitMap (projection F i)).hom x := rfl

end GrpCat.FilteredColimits.FiniteProducts
