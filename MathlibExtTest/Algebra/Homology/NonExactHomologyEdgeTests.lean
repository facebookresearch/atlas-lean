/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# A left-exact homology edge which is not an isomorphism

For the short complex `ℤ —2→ ℤ → 0`, the homology is computed as `ZMod 2` from the actual
cokernel universal property. Apply the left-exact functor `Hom_ℤ(ZMod 2, −)`.

Every homomorphism from `ZMod 2` to the integers is zero. Consequently the mapped complex has
zero homology, whereas the Hom group of the original homology contains the nonzero identity.
The cycles comparison is still an isomorphism, but the general left-exact homology edge is the
zero map to a nonzero group and is not an isomorphism. The same functor does not preserve the
epimorphism `ℤ → ZMod 2`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace MathlibExtTest.NonExactHomologyEdge

private abbrev E := ModuleCat.{0} ℤ
private abbrev N : E := ModuleCat.of ℤ ℤ
private abbrev T : E := ModuleCat.of ℤ (ZMod 2)
private abbrev Z : E := 0

private def twice : N ⟶ N := ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)

private def reduction : N ⟶ T :=
  ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap

private theorem exact_twice_reduction : Function.Exact twice.hom reduction.hom := by
  intro x
  change (x : ZMod 2) = 0 ↔ ∃ y : ℤ, (2 : ℤ) • y = x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    exact ⟨y, by simpa only [smul_eq_mul, eq_comm] using hy⟩
  · rintro ⟨y, hy⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mpr
    exact ⟨y, by simpa only [smul_eq_mul, eq_comm] using hy⟩

private theorem reduction_surjective : Function.Surjective reduction.hom := by
  change Function.Surjective (fun x : ℤ => (x : ZMod 2))
  exact ZMod.intCast_surjective

private theorem twice_reduction : twice ≫ reduction = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact exact_twice_reduction.apply_apply_eq_zero x

private def S : ShortComplex E := ShortComplex.mk twice (0 : N ⟶ Z) (by simp)

private def homologyCoordinate : S.homology ≅ T :=
  (ShortComplex.HomologyData.ofIsColimitCokernelCofork S rfl
    (CokernelCofork.ofπ reduction twice_reduction)
    (ModuleCat.isColimitCokernelCofork twice reduction
      exact_twice_reduction reduction_surjective)).left.homologyIso

private abbrev F : E ⥤ AddCommGrpCat.{0} := preadditiveCoyoneda.obj (op T)

private theorem hom_to_integer_zero (f : T ⟶ N) : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f.hom x : ℤ) = 0
  have hx : (2 : ℤ) • x = 0 := by
    change (2 : ZMod 2) * (x : ZMod 2) = 0
    norm_num
  have hfx : (2 : ℤ) • f.hom x = 0 := by
    rw [← f.hom.map_smul, hx, map_zero]
  have hmul : 2 * f.hom x = 0 := by simpa only [smul_eq_mul] using hfx
  change (2 : ℤ) * (f.hom x : ℤ) = 0 at hmul
  omega

private theorem mapped_middle_isZero : IsZero (F.obj N) := by
  let _ : Subsingleton (T ⟶ N) := ⟨fun f g =>
    (hom_to_integer_zero f).trans (hom_to_integer_zero g).symm⟩
  change IsZero (AddCommGrpCat.of (T ⟶ N))
  exact AddCommGrpCat.isZero_of_subsingleton _

private theorem endomorphism_group_not_isZero : ¬ IsZero (F.obj T) := by
  intro h
  let _ : Subsingleton (T ⟶ T) := AddCommGrpCat.subsingleton_of_isZero h
  have hid : (𝟙 T : T ⟶ T) = 0 := Subsingleton.elim _ _
  have hv := congrArg (fun f : T ⟶ T => f.hom 1) hid
  change (1 : ZMod 2) = 0 at hv
  exact (by decide : (1 : ZMod 2) ≠ 0) hv

private theorem mapped_homology_isZero : IsZero (S.map F).homology :=
  (S.map F).isZero_homology_of_isZero_X₂ mapped_middle_isZero

private theorem hom_of_original_homology_not_isZero : ¬ IsZero (F.obj S.homology) := by
  intro h
  exact endomorphism_group_not_isZero (h.of_iso (F.mapIso homologyCoordinate).symm)

example : twice.hom 1 = 2 := by norm_num [twice, smul_eq_mul]

example : Epi reduction := (ModuleCat.epi_iff_surjective _).mpr reduction_surjective

example : IsZero (F.obj N) := mapped_middle_isZero

example : IsZero (S.map F).homology := mapped_homology_isZero

example : ¬ IsZero (F.obj S.homology) := hom_of_original_homology_not_isZero

example : IsIso (ShortComplex.leftExactCyclesComparison F S) := inferInstance

example : ShortComplex.leftExactHomologyEdge F S = 0 :=
  mapped_homology_isZero.eq_zero_of_src _

example : ¬ IsIso (ShortComplex.leftExactHomologyEdge F S) := by
  intro h
  let _ : IsIso (ShortComplex.leftExactHomologyEdge F S) := h
  exact hom_of_original_homology_not_isZero
    (mapped_homology_isZero.of_iso (asIso (ShortComplex.leftExactHomologyEdge F S)).symm)

example : F.map reduction = 0 := mapped_middle_isZero.eq_zero_of_src _

example : ¬ Epi (F.map reduction) := by
  intro h
  obtain ⟨f, hf⟩ := (AddCommGrpCat.epi_iff_surjective (F.map reduction)).mp h (𝟙 T)
  have hz : f = 0 := hom_to_integer_zero f
  rw [hz, map_zero] at hf
  have hv := congrArg (fun f : T ⟶ T => f.hom 1) hf
  change (0 : ZMod 2) = 1 at hv
  exact (by decide : (0 : ZMod 2) ≠ 1) hv

end MathlibExtTest.NonExactHomologyEdge
