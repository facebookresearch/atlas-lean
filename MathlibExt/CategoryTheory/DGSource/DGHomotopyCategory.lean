/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/HomotopyCategory.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import MathlibExt.CategoryTheory.DGSource.DGCategory

/-!
# The homotopy category of a differential graded category

For a differential graded category C, the morphisms in its homotopy category are the
degree-zero cocycles in each Hom complex, modulo the degree-zero coboundaries. Composition is
induced by differential graded composition. The Leibniz rule shows that composing a boundary
with a cycle on either side is again a boundary, so composition descends to cohomology classes.

This file uses Mathlib's canonical homology object for that quotient. It records the concrete
criterion that two closed degree-zero morphisms determine the same morphism precisely when their
difference is the differential of a degree-minus-one morphism, and that a chain map between Hom
complexes acts on homotopy classes through representatives. The resulting category is naturally
preadditive and linear over the ground ring.

## Main definitions

* MathlibExt.DGSource.dgCycles: the degree-zero cocycles in a DG Hom complex.
* MathlibExt.DGSource.dgBoundaries: the degree-zero coboundaries in a DG Hom complex.
* MathlibExt.DGSource.DGHomotopyClass: the canonical degree-zero homology of a DG Hom complex.
* MathlibExt.DGSource.dgHomotopyComp: composition of homotopy classes.
* MathlibExt.DGSource.DGHomotopyCategory: the category with the objects of a DG category and morphisms
  given by DGHomotopyClass.

## Main results

* `MathlibExt.DGSource.exactAt_iff_forall_exists_dgDifferential_eq`: a Hom complex is exact in a degree
  exactly when every cycle of that degree is a boundary.
* `MathlibExt.DGSource.dgHomotopyClass_eq_iff`: two cocycles have the same class exactly when their difference
  is a coboundary.
* `MathlibExt.DGSource.dgHomotopyClass_eq_homologyπ`: a homotopy class is the image of any lifting cycle under
  Mathlib's `HomologicalComplex.homologyπ`.
* `MathlibExt.DGSource.homologyMap_dgHomotopyClass`: a chain map of Hom complexes sends the class of `f` to the
  class of the image of `f`.
* `MathlibExt.DGSource.DGHomotopyCategory.isZero_of_iff_dgId_mem_dgBoundaries`: an object is zero in the
  homotopy category exactly when its identity is a coboundary.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
* `TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology` (not ported here), the formal template
  for the quotient construction and descended bilinear operation.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

noncomputable section

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Cycles, boundaries, and homotopy classes -/

/-- The degree-zero cocycles in the Hom complex from X to Y. -/
def dgCycles (X Y : C) : Submodule R (DGHom R 0 X Y) :=
  LinearMap.ker (dgDifferential R 0)

/-- A degree-zero morphism is a cocycle exactly when its differential vanishes. -/
@[simp]
theorem mem_dgCycles {X Y : C} {f : DGHom R 0 X Y} :
    f ∈ dgCycles R X Y ↔ dgDifferential R 0 f = 0 :=
  LinearMap.mem_ker

/-- The degree-zero coboundaries in the Hom complex from X to Y. -/
def dgBoundaries (X Y : C) : Submodule R (DGHom R 0 X Y) :=
  LinearMap.range (dgDifferential R (-1))

/-- A degree-zero morphism is a coboundary exactly when it is the differential of a
degree-minus-one morphism. -/
@[simp]
theorem mem_dgBoundaries {X Y : C} {f : DGHom R 0 X Y} :
    f ∈ dgBoundaries R X Y ↔
      ∃ h : DGHom R (-1) X Y, dgDifferential R (-1) h = f :=
  LinearMap.mem_range

/-- Every degree-zero coboundary is a cocycle. -/
theorem dgBoundaries_le_dgCycles (X Y : C) :
    dgBoundaries R X Y ≤ dgCycles R X Y := by
  rintro _ ⟨h, rfl⟩
  exact dgDifferential_dgDifferential R h

/-- A Hom complex is exact in degree `p + 1` exactly when every cycle of degree `p + 1` is a
boundary. -/
theorem exactAt_iff_forall_exists_dgDifferential_eq {X Y : C} {p : ℤ} :
    (dgHomComplex R X Y).ExactAt (p + 1) ↔ ∀ z : DGHom R (p + 1) X Y,
      dgDifferential R (p + 1) z = 0 → ∃ g : DGHom R p X Y, dgDifferential R p g = z := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  -- The maps of the short complex `sc'` are the differentials, by definition.
  rfl

private noncomputable def dgCyclesConcreteEquiv (X Y : C) :
    dgCycles R X Y ≃ₗ[R]
      ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.K :=
  { toFun := fun f ↦ by
      -- `moduleCatLeftHomologyData.K` unfolds to the kernel of the middle differential,
      -- which is `dgCycles` after unfolding `dgHomComplex` in degree zero.
      change LinearMap.ker (dgDifferential R 0)
      exact f
    invFun := fun f ↦ by
      exact f
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

/-- A morphism in H⁰(C), using the canonical Mathlib homology object of the DG Hom complex. -/
noncomputable abbrev DGHomotopyClass (X Y : C) :=
  (dgHomComplex R X Y).homology 0

private noncomputable def dgHomologyIso (X Y : C) :
    DGHomotopyClass R X Y ≅
      ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.H :=
  (dgHomComplex R X Y).homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatHomologyIso

/-- The linear quotient map from degree-zero cocycles to homotopy classes. -/
noncomputable def dgHomotopyClassLinearMap (X Y : C) :
    dgCycles R X Y →ₗ[R] DGHomotopyClass R X Y :=
  let S := (dgHomComplex R X Y).sc' (-1) 0 1
  (dgHomologyIso R X Y).inv.hom.comp
    (S.moduleCatLeftHomologyData.π.hom.comp (dgCyclesConcreteEquiv R X Y).toLinearMap)

/-- The homotopy class represented by a closed degree-zero morphism. -/
def dgHomotopyClass {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    DGHomotopyClass R X Y :=
  dgHomotopyClassLinearMap R X Y ⟨f, hf⟩

/-- Under Mathlib's concrete homology isomorphism, a homotopy class is the quotient class of its
cocycle representative. -/
private theorem dgHomotopyClass_moduleCatHomologyIso_hom {X Y : C}
    (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    let S := (dgHomComplex R X Y).sc' (-1) 0 1
    (dgHomologyIso R X Y).hom (dgHomotopyClass R f hf) =
      S.moduleCatLeftHomologyData.π (dgCyclesConcreteEquiv R X Y ⟨f, hf⟩) := by
  let e := dgHomologyIso R X Y
  -- Unfolding `dgHomotopyClassLinearMap` exposes transport by `e.inv`; applying `e.hom`
  -- then reduces the claim to the inverse-hom identity.
  change e.hom (e.inv _) = _
  exact e.inv_hom_id_apply _

private theorem mem_moduleCatToCycles_range {X Y : C} (f : dgCycles R X Y) :
    dgCyclesConcreteEquiv R X Y f ∈
        LinearMap.range
          ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatToCycles ↔
      (f : DGHom R 0 X Y) ∈ dgBoundaries R X Y := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    exact congrArg Subtype.val hh
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hh

private theorem moduleCatπ_eq_zero_iff {X Y : C}
    (f : ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.K) :
    ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π f = 0 ↔
      f ∈ LinearMap.range
        ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatToCycles := by
  -- For `ModuleCat`, the concrete homology projection is definitionally the quotient map
  -- by the range of the map into cycles.
  change Submodule.Quotient.mk f = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero
    (LinearMap.range ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatToCycles)

/-- Zero represents zero as a homotopy class. -/
@[simp]
theorem dgHomotopyClass_zero (X Y : C) :
    dgHomotopyClass R (0 : DGHom R 0 X Y) (dgCycles R X Y).zero_mem = 0 :=
  (dgHomotopyClassLinearMap R X Y).map_zero

/-- The class of a sum of cocycles is the sum of their classes. -/
@[simp]
theorem dgHomotopyClass_add {X Y : C} (f g : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    dgHomotopyClass R (f + g) ((dgCycles R X Y).add_mem hf hg) =
      dgHomotopyClass R f hf + dgHomotopyClass R g hg :=
  (dgHomotopyClassLinearMap R X Y).map_add ⟨f, hf⟩ ⟨g, hg⟩

/-- The class of a scalar multiple of a cocycle is the scalar multiple of its class. -/
@[simp]
theorem dgHomotopyClass_smul {X Y : C} (r : R) (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R (r • f) ((dgCycles R X Y).smul_mem r hf) =
      r • dgHomotopyClass R f hf :=
  (dgHomotopyClassLinearMap R X Y).map_smul r ⟨f, hf⟩

/-- Every homotopy class has a closed degree-zero representative. -/
theorem exists_dgHomotopyClass_eq {X Y : C} (c : DGHomotopyClass R X Y) :
    ∃ (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y), dgHomotopyClass R f hf = c := by
  let e := dgHomologyIso R X Y
  let S := (dgHomComplex R X Y).sc' (-1) 0 1
  obtain ⟨f, hf⟩ : ∃ f, S.moduleCatLeftHomologyData.π f = e.hom c := by
    induction e.hom c using Submodule.Quotient.induction_on with
    | H f => exact ⟨f, rfl⟩
  let g := (dgCyclesConcreteEquiv R X Y).symm f
  refine ⟨g, g.2, ?_⟩
  apply e.toLinearEquiv.injective
  have hclass := dgHomotopyClass_moduleCatHomologyIso_hom R (g : DGHom R 0 X Y) g.2
  -- The function underlying `e.toLinearEquiv` is `e.hom`; spelling that out lets the
  -- representative compatibility lemma rewrite the transported class.
  change e.hom (dgHomotopyClass R g g.2) = e.hom c
  rw [show e.hom (dgHomotopyClass R g g.2) =
    S.moduleCatLeftHomologyData.π (dgCyclesConcreteEquiv R X Y g) by
      simpa only [e, S] using hclass]
  simpa only [g, LinearEquiv.apply_symm_apply] using hf

/-- Two closed degree-zero morphisms represent the same homotopy class exactly when their
difference is a coboundary. -/
@[simp]
theorem dgHomotopyClass_eq_iff {X Y : C} {f g : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = dgHomotopyClass R g hg ↔
      f - g ∈ dgBoundaries R X Y := by
  let e := dgHomologyIso R X Y
  constructor
  · intro h
    have h' := congrArg e.hom h
    have hf' := dgHomotopyClass_moduleCatHomologyIso_hom R f hf
    have hg' := dgHomotopyClass_moduleCatHomologyIso_hom R g hg
    -- Applying the bundled isomorphism is definitionally application of its forward map.
    -- The following rewrites then use the explicit representative compatibility lemma.
    change e.hom (dgHomotopyClass R f hf) = e.hom (dgHomotopyClass R g hg) at h'
    rw [show e.hom (dgHomotopyClass R f hf) =
        ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π
          (dgCyclesConcreteEquiv R X Y ⟨f, hf⟩) by
          simpa only [e] using hf',
      show e.hom (dgHomotopyClass R g hg) =
        ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π
          (dgCyclesConcreteEquiv R X Y ⟨g, hg⟩) by
          simpa only [e] using hg'] at h'
    let fg : dgCycles R X Y := ⟨f, hf⟩ - ⟨g, hg⟩
    have hzero : ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π
        (dgCyclesConcreteEquiv R X Y fg) = 0 := by
      rw [show dgCyclesConcreteEquiv R X Y fg =
        dgCyclesConcreteEquiv R X Y ⟨f, hf⟩ -
          dgCyclesConcreteEquiv R X Y ⟨g, hg⟩ by simp only [fg, map_sub],
        map_sub, h', sub_self]
    have hrange := (moduleCatπ_eq_zero_iff R _).1 hzero
    simpa only [fg, Submodule.coe_sub] using
      (mem_moduleCatToCycles_range R fg).1 hrange
  · intro h
    apply e.toLinearEquiv.injective
    have hf' := dgHomotopyClass_moduleCatHomologyIso_hom R f hf
    have hg' := dgHomotopyClass_moduleCatHomologyIso_hom R g hg
    -- As above, expose the forward map of the concrete homology isomorphism before using
    -- `dgHomotopyClass_moduleCatHomologyIso_hom`.
    change e.hom (dgHomotopyClass R f hf) = e.hom (dgHomotopyClass R g hg)
    rw [show e.hom (dgHomotopyClass R f hf) =
        ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π
          (dgCyclesConcreteEquiv R X Y ⟨f, hf⟩) by
          simpa only [e] using hf',
      show e.hom (dgHomotopyClass R g hg) =
        ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π
          (dgCyclesConcreteEquiv R X Y ⟨g, hg⟩) by
          simpa only [e] using hg']
    rw [← sub_eq_zero, ← map_sub]
    let fg : dgCycles R X Y := ⟨f, hf⟩ - ⟨g, hg⟩
    apply (moduleCatπ_eq_zero_iff R _).2
    apply (mem_moduleCatToCycles_range R fg).2
    simpa only [fg, Submodule.coe_sub] using h

/-- A closed degree-zero morphism represents zero exactly when it is a coboundary. -/
@[simp]
theorem dgHomotopyClass_eq_zero_iff {X Y : C} {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = 0 ↔ f ∈ dgBoundaries R X Y := by
  rw [← dgHomotopyClass_zero R X Y]
  simpa only [sub_zero] using dgHomotopyClass_eq_iff R hf (dgCycles R X Y).zero_mem

/-! ### Comparison with Mathlib's homology projection -/

/- The homotopy class of a closed degree-zero morphism is the image under Mathlib's homology
projection of an explicit cycle lifting it. -/
private theorem exists_iCycles_eq_and_dgHomotopyClass_eq {X Y : C} (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    ∃ x : (dgHomComplex R X Y).cycles 0, ((dgHomComplex R X Y).iCycles 0).hom x = f ∧
      dgHomotopyClass R f hf = ((dgHomComplex R X Y).homologyπ 0).hom x := by
  let K := dgHomComplex R X Y
  let S := K.sc' (-1) 0 1
  let e := K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)
  let c : S.moduleCatLeftHomologyData.K := ⟨f, hf⟩
  refine ⟨(S.moduleCatCyclesIso.inv ≫ e.inv).hom c, ?_, ?_⟩
  · have h : (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.iCycles 0 =
        S.moduleCatLeftHomologyData.i := by
      rw [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
      exact S.moduleCatCyclesIso_inv_iCycles
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c
  · have h : S.moduleCatLeftHomologyData.π ≫
        (S.moduleCatHomologyIso.inv ≫ (K.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).inv) =
        (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.homologyπ 0 := by
      rw [← Category.assoc, ← S.moduleCatCyclesIso_inv_π, Category.assoc, Category.assoc,
        HomologicalComplex.π_homologyIsoSc'_inv]
    -- `dgHomotopyClass R f hf` is by definition the left-hand side of `h` applied to `c`.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c

/-- The homotopy class of a closed degree-zero morphism `f` is the image, under Mathlib's
projection `HomologicalComplex.homologyπ` from cycles to homology, of any cycle lifting `f`. -/
theorem dgHomotopyClass_eq_homologyπ {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgCycles R X Y)
    (x : (dgHomComplex R X Y).cycles 0) (hx : ((dgHomComplex R X Y).iCycles 0).hom x = f) :
    dgHomotopyClass R f hf = ((dgHomComplex R X Y).homologyπ 0).hom x := by
  obtain ⟨y, hy, hclass⟩ := exists_iCycles_eq_and_dgHomotopyClass_eq R f hf
  rw [hclass, (ModuleCat.mono_iff_injective ((dgHomComplex R X Y).iCycles 0)).1 inferInstance
    (hy.trans hx.symm)]

/-- A closed degree-zero morphism stays closed under a chain map of Hom complexes. -/
theorem map_mem_dgCycles {C' : Type*} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) : (φ.f 0).hom f ∈ dgCycles R X' Y' := by
  obtain ⟨x, hx, _⟩ := exists_iCycles_eq_and_dgHomotopyClass_eq R f hf
  rw [← hx, ← ModuleCat.comp_apply, ← HomologicalComplex.cyclesMap_i,
    ModuleCat.comp_apply, mem_dgCycles]
  unfold dgDifferential
  rw [← ModuleCat.comp_apply, zero_add, (dgHomComplex R X' Y').iCycles_d 0 1]
  rfl

/-- The map induced on homotopy classes by a chain map of Hom complexes sends the class of a
closed degree-zero morphism to the class of its image. -/
@[simp]
theorem homologyMap_dgHomotopyClass {C' : Type*} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) :
    (HomologicalComplex.homologyMap φ 0).hom (dgHomotopyClass R f hf) =
      dgHomotopyClass R ((φ.f 0).hom f) (map_mem_dgCycles R φ hf) := by
  obtain ⟨x, hx, hclass⟩ := exists_iCycles_eq_and_dgHomotopyClass_eq R f hf
  rw [hclass, dgHomotopyClass_eq_homologyπ R _ ((HomologicalComplex.cyclesMap φ 0).hom x),
    ← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  rw [← hx, ← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]

/-! ### Composition on homotopy classes -/

/-- Composition of two degree-zero DG morphisms. -/
def dgCompZero {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    DGHom R 0 X Z :=
  dgComp R f g (zero_add 0)

/-- Composition of degree-zero DG morphisms is homogeneous DG composition in degree zero. -/
theorem dgCompZero_def {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R f g = dgComp R f g (zero_add 0) :=
  (rfl)

/-- Composition of degree-zero DG morphisms is additive in its first argument. -/
@[simp]
theorem add_dgCompZero {X Y Z : C} (f f' : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R (f + f') g = dgCompZero R f g + dgCompZero R f' g := by
  simp only [dgCompZero_def, add_dgComp]

/-- Composition of degree-zero DG morphisms respects scalar multiplication in its first
argument. -/
@[simp]
theorem smul_dgCompZero {X Y Z : C} (r : R) (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R (r • f) g = r • dgCompZero R f g := by
  simp only [dgCompZero_def, smul_dgComp]

/-- Composition of degree-zero DG morphisms is additive in its second argument. -/
@[simp]
theorem dgCompZero_add {X Y Z : C} (f : DGHom R 0 X Y) (g g' : DGHom R 0 Y Z) :
    dgCompZero R f (g + g') = dgCompZero R f g + dgCompZero R f g' := by
  simp only [dgCompZero_def, dgComp_add]

/-- Composition of degree-zero DG morphisms respects scalar multiplication in its second
argument. -/
@[simp]
theorem dgCompZero_smul {X Y Z : C} (r : R) (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R f (r • g) = r • dgCompZero R f g := by
  simp only [dgCompZero_def, dgComp_smul]

/-- The composite of two degree-zero cocycles is a degree-zero cocycle. -/
theorem dgCompZero_mem_dgCycles {X Y Z : C} {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgCompZero R f g ∈ dgCycles R X Z := by
  rw [dgCompZero_def, mem_dgCycles, dgDifferential_dgComp,
    (mem_dgCycles R).mp hf, (mem_dgCycles R).mp hg]
  simp

/-- Composing a degree-zero boundary on the left with a degree-zero cocycle gives a boundary. -/
theorem dgCompZero_mem_dgBoundaries_of_left {X Y Z : C}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgBoundaries R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgCompZero R f g ∈ dgBoundaries R X Z := by
  obtain ⟨h, rfl⟩ := hf
  refine ⟨dgComp R h g (add_zero (-1)), ?_⟩
  rw [dgDifferential_dgComp, (mem_dgCycles R).mp hg]
  simp only [dgComp_zero, smul_zero, add_zero, dgCompZero_def]

/-- Composing a degree-zero cocycle on the left with a degree-zero boundary gives a boundary. -/
theorem dgCompZero_mem_dgBoundaries_of_right {X Y Z : C}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgBoundaries R Y Z) :
    dgCompZero R f g ∈ dgBoundaries R X Z := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨dgComp R f h (zero_add (-1)), ?_⟩
  rw [dgDifferential_dgComp, (mem_dgCycles R).mp hf]
  simp only [zero_dgComp, zero_add, Int.negOnePow_zero, one_smul, dgCompZero_def]

/-- Composition restricted to degree-zero cocycles. -/
def dgCyclesComp (X Y Z : C) :
    dgCycles R X Y →ₗ[R] dgCycles R Y Z →ₗ[R] dgCycles R X Z :=
  LinearMap.mk₂ R
    (fun (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦
      ⟨dgCompZero R (X := X) (Y := Y) (Z := Z)
        (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z), dgCompZero_mem_dgCycles R f.2 g.2⟩)
    (fun (f f' : dgCycles R X Y) (g : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_add, add_dgCompZero])
    (fun r (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_smul, smul_dgCompZero])
    (fun (f : dgCycles R X Y) (g g' : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_add, dgCompZero_add])
    (fun r (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_smul, dgCompZero_smul])

/-- The underlying morphism of the composite of two cocycles is their DG composition. -/
@[simp]
theorem coe_dgCyclesComp {X Y Z : C} (f : dgCycles R X Y) (g : dgCycles R Y Z) :
    (dgCyclesComp R X Y Z f g : DGHom R 0 X Z) =
      dgCompZero R (X := X) (Y := Y) (Z := Z) f g :=
  (rfl)

/-- Composition of homotopy classes, obtained by descending DG composition through the
coboundary quotients. -/
private def dgConcreteCyclesComp (X Y Z : C) :
    ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.K →ₗ[R]
      ((dgHomComplex R Y Z).sc' (-1) 0 1).moduleCatLeftHomologyData.K →ₗ[R]
        ((dgHomComplex R X Z).sc' (-1) 0 1).moduleCatLeftHomologyData.K :=
  LinearMap.mk₂ R
    (fun f g ↦ dgCyclesConcreteEquiv R X Z
      (dgCyclesComp R X Y Z ((dgCyclesConcreteEquiv R X Y).symm f)
        ((dgCyclesConcreteEquiv R Y Z).symm g)))
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)

private def dgConcreteHomotopyComp (X Y Z : C) :
    ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.H →ₗ[R]
      ((dgHomComplex R Y Z).sc' (-1) 0 1).moduleCatLeftHomologyData.H →ₗ[R]
        ((dgHomComplex R X Z).sc' (-1) 0 1).moduleCatLeftHomologyData.H :=
  let SXY := (dgHomComplex R X Y).sc' (-1) 0 1
  let SYZ := (dgHomComplex R Y Z).sc' (-1) 0 1
  let SXZ := (dgHomComplex R X Z).sc' (-1) 0 1
  ((dgConcreteCyclesComp R X Y Z).compr₂ SXZ.moduleCatLeftHomologyData.π.hom).liftQ₂
    (LinearMap.range SXY.moduleCatToCycles) (LinearMap.range SYZ.moduleCatToCycles)
    (fun f hf ↦ LinearMap.ext fun g ↦ (moduleCatπ_eq_zero_iff R _).2 <| by
      apply (mem_moduleCatToCycles_range R
        ((dgCyclesConcreteEquiv R X Z).symm
          (dgConcreteCyclesComp R X Y Z f g))).2
      simp only [dgConcreteCyclesComp]
      exact dgCompZero_mem_dgBoundaries_of_left R
        (by
          obtain ⟨h, hh⟩ := hf
          refine ⟨h, ?_⟩
          exact congrArg Subtype.val hh)
        ((dgCyclesConcreteEquiv R Y Z).symm g).2)
    (fun g hg ↦ LinearMap.ext fun f ↦ (moduleCatπ_eq_zero_iff R _).2 <| by
      apply (mem_moduleCatToCycles_range R
        ((dgCyclesConcreteEquiv R X Z).symm
          (dgConcreteCyclesComp R X Y Z f g))).2
      simp only [dgConcreteCyclesComp]
      exact dgCompZero_mem_dgBoundaries_of_right R
        ((dgCyclesConcreteEquiv R X Y).symm f).2
        (by
          obtain ⟨h, hh⟩ := hg
          refine ⟨h, ?_⟩
          exact congrArg Subtype.val hh))

/-- The bilinear composition of homotopy classes induced by DG composition. -/
noncomputable def dgHomotopyComp (X Y Z : C) :
    DGHomotopyClass R X Y →ₗ[R] DGHomotopyClass R Y Z →ₗ[R]
      DGHomotopyClass R X Z :=
  LinearMap.mk₂ R
    (fun f g ↦ (dgHomologyIso R X Z).inv
      (dgConcreteHomotopyComp R X Y Z ((dgHomologyIso R X Y).hom f)
        ((dgHomologyIso R Y Z).hom g)))
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp)

/-- The composite of classes is represented by the DG composite of their representatives. -/
@[simp]
theorem dgHomotopyComp_dgHomotopyClass {X Y Z : C}
    (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgHomotopyComp R X Y Z (dgHomotopyClass R f hf) (dgHomotopyClass R g hg) =
      dgHomotopyClass R (dgCompZero R f g) (dgCompZero_mem_dgCycles R hf hg) := by
  let eXY := dgHomologyIso R X Y
  let eYZ := dgHomologyIso R Y Z
  let eXZ := dgHomologyIso R X Z
  have hf' := dgHomotopyClass_moduleCatHomologyIso_hom R f hf
  have hg' := dgHomotopyClass_moduleCatHomologyIso_hom R g hg
  have hfg' := dgHomotopyClass_moduleCatHomologyIso_hom R (dgCompZero R f g)
    (dgCompZero_mem_dgCycles R hf hg)
  apply eXZ.toLinearEquiv.injective
  -- Unfolding `dgHomotopyComp` exposes its construction by transporting the concrete
  -- quotient composition along `eXY`, `eYZ`, and `eXZ`.
  change eXZ.hom (eXZ.inv
      (dgConcreteHomotopyComp R X Y Z
        (eXY.hom (dgHomotopyClass R f hf))
        (eYZ.hom (dgHomotopyClass R g hg)))) =
    eXZ.hom (dgHomotopyClass R (dgCompZero R f g) _)
  rw [eXZ.inv_hom_id_apply]
  rw [show eXY.hom (dgHomotopyClass R f hf) =
      ((dgHomComplex R X Y).sc' (-1) 0 1).moduleCatLeftHomologyData.π
        (dgCyclesConcreteEquiv R X Y ⟨f, hf⟩) by simpa only [eXY] using hf',
    show eYZ.hom (dgHomotopyClass R g hg) =
      ((dgHomComplex R Y Z).sc' (-1) 0 1).moduleCatLeftHomologyData.π
        (dgCyclesConcreteEquiv R Y Z ⟨g, hg⟩) by simpa only [eYZ] using hg',
    show eXZ.hom (dgHomotopyClass R (dgCompZero R f g) _) =
      ((dgHomComplex R X Z).sc' (-1) 0 1).moduleCatLeftHomologyData.π
        (dgCyclesConcreteEquiv R X Z
          ⟨dgCompZero R f g, dgCompZero_mem_dgCycles R hf hg⟩) by
            simpa only [eXZ] using hfg']
  rfl

/-- Composition of homotopy classes is associative. -/
theorem dgHomotopyComp_assoc {W X Y Z : C}
    (f : DGHomotopyClass R W X) (g : DGHomotopyClass R X Y)
    (h : DGHomotopyClass R Y Z) :
    dgHomotopyComp R W Y Z (dgHomotopyComp R W X Y f g) h =
      dgHomotopyComp R W X Z f (dgHomotopyComp R X Y Z g h) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
  obtain ⟨g, hg, rfl⟩ := exists_dgHomotopyClass_eq R g
  obtain ⟨h, hh, rfl⟩ := exists_dgHomotopyClass_eq R h
  simp only [dgHomotopyComp_dgHomotopyClass]
  apply congrArg (dgHomotopyClassLinearMap R W Z)
  apply Subtype.ext
  exact dgComp_assoc R f g h rfl rfl rfl

/-! ### The category H⁰(C) -/

/-- The homotopy category of a differential graded category. It has the same objects as C and
the zeroth cohomology of each DG Hom complex as its morphisms. -/
structure DGHomotopyCategory (R : Type v) (C : Type u) where
  /-- The underlying object of the differential graded category. -/
  obj : C

namespace DGHomotopyCategory

/-- Regard an object of a DG category as an object of its homotopy category. -/
@[expose] def of (X : C) : DGHomotopyCategory R C := ⟨X⟩

/-- Regard an object of a DG homotopy category as an object of the underlying DG category. -/
@[expose] def underlying (X : DGHomotopyCategory R C) : C := X.obj

omit [CommRing R] [DGCategory R C] in
@[simp]
theorem underlying_of (X : C) : underlying R (of R X) = X := (rfl)

omit [CommRing R] [DGCategory R C] in
@[simp]
theorem of_underlying (X : DGHomotopyCategory R C) : of R (underlying R X) = X := by
  cases X
  rfl

omit [CommRing R] [DGCategory R C] in
/-- Every object of the DG homotopy category comes from an object of the DG category. -/
theorem of_surjective : Function.Surjective (of R : C → DGHomotopyCategory R C) :=
  fun X ↦ ⟨underlying R X, of_underlying R X⟩

omit [CommRing R] [DGCategory R C] in
/-- Objects of the DG homotopy category are equal when their underlying DG objects are equal. -/
@[ext]
theorem ext {X Y : DGHomotopyCategory R C} (h : underlying R X = underlying R Y) : X = Y := by
  rw [← of_underlying R X, ← of_underlying R Y, h]

instance : Quiver (DGHomotopyCategory R C) where
  Hom X Y := DGHomotopyClass R (underlying R X) (underlying R Y)

noncomputable instance : Category (DGHomotopyCategory R C) where
  id X := dgHomotopyClass R (dgId R (underlying R X))
    ((mem_dgCycles R).mpr (dgDifferential_dgId R (underlying R X)))
  comp {X Y Z} f g :=
    dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f g
  id_comp {X Y} f := by
    obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
    simp only [dgHomotopyComp_dgHomotopyClass]
    apply congrArg (dgHomotopyClassLinearMap R (underlying R X) (underlying R Y))
    apply Subtype.ext
    exact dgId_dgComp R f
  comp_id {X Y} f := by
    obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
    simp only [dgHomotopyComp_dgHomotopyClass]
    apply congrArg (dgHomotopyClassLinearMap R (underlying R X) (underlying R Y))
    apply Subtype.ext
    exact dgComp_dgId R f
  assoc {W X Y Z} f g h := dgHomotopyComp_assoc R f g h

noncomputable instance : Preadditive (DGHomotopyCategory R C) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (DGHomotopyClass R (underlying R X) (underlying R Y)))
  add_comp X Y Z f f' g :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z)).map_add₂ f f' g
  comp_add X Y Z f g g' :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f).map_add g g'

noncomputable instance : Linear R (DGHomotopyCategory R C) where
  homModule X Y := inferInstanceAs
    (Module R (DGHomotopyClass R (underlying R X) (underlying R Y)))
  smul_comp X Y Z r f g :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z)).map_smul₂ r f g
  comp_smul X Y Z f r g :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f).map_smul r g

/-- Composition in the homotopy category is the composition `MathlibExt.DGSource.dgHomotopyComp` of homotopy
classes. -/
theorem comp_def {X Y Z : DGHomotopyCategory R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f g :=
  (rfl)

/-- The identity of the homotopy category is the homotopy class of the DG identity. -/
theorem id_def (X : DGHomotopyCategory R C) :
    𝟙 X = dgHomotopyClass R (dgId R (underlying R X))
      ((mem_dgCycles R).mpr (dgDifferential_dgId R (underlying R X))) :=
  (rfl)

/-- A closed degree-zero DG morphism, regarded as a morphism in the homotopy category. -/
def homOf {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    of R X ⟶ of R Y :=
  dgHomotopyClass R f hf

/-- A closed degree-zero DG morphism, regarded in the homotopy category, is its homotopy
class. -/
theorem homOf_def {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    homOf R f hf = dgHomotopyClass R f hf :=
  (rfl)

/-- The zero DG morphism represents the zero morphism in the homotopy category. -/
@[simp]
theorem homOf_zero (X Y : C) :
    homOf R (0 : DGHom R 0 X Y) (dgCycles R X Y).zero_mem = 0 :=
  dgHomotopyClass_zero R X Y

/-- Taking a morphism to the homotopy category preserves addition. -/
@[simp]
theorem homOf_add {X Y : C} (f g : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    homOf R (f + g) ((dgCycles R X Y).add_mem hf hg) = homOf R f hf + homOf R g hg :=
  dgHomotopyClass_add R f g hf hg

/-- Taking a morphism to the homotopy category preserves scalar multiplication. -/
@[simp]
theorem homOf_smul {X Y : C} (r : R) (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    homOf R (r • f) ((dgCycles R X Y).smul_mem r hf) = r • homOf R f hf :=
  dgHomotopyClass_smul R r f hf

/-- Every morphism of the homotopy category is the class of a closed degree-zero DG morphism. -/
theorem exists_homOf_eq {X Y : C} (f : of R X ⟶ of R Y) :
    ∃ (g : DGHom R 0 X Y) (hg : g ∈ dgCycles R X Y), homOf R g hg = f :=
  exists_dgHomotopyClass_eq R f

/-- Taking a morphism to the homotopy category preserves negation. -/
@[simp]
theorem homOf_neg {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    homOf R (-f) ((dgCycles R X Y).neg_mem hf) = -homOf R f hf := by
  rw [eq_neg_iff_add_eq_zero, ← homOf_add, ← homOf_zero]
  congr 1
  exact neg_add_cancel f

/-- Taking a morphism to the homotopy category preserves multiplication by a sign. -/
@[simp]
theorem homOf_units_smul {X Y : C} (u : ℤˣ) (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    homOf R (u • f) ((dgCycles R X Y).toAddSubgroup.zsmul_mem hf (u : ℤ)) = u • homOf R f hf := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    exact homOf_neg R f hf

/-- A closed degree-zero DG morphism represents zero precisely when it is a boundary. -/
@[simp]
theorem homOf_eq_zero_iff {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgCycles R X Y) :
    homOf R f hf = 0 ↔ f ∈ dgBoundaries R X Y :=
  dgHomotopyClass_eq_zero_iff R hf

/-- The DG identity represents the identity in the homotopy category. -/
@[simp]
theorem homOf_dgId (X : C) :
    homOf R (dgId R X) ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) = 𝟙 (of R X) :=
  (rfl)

/-- Two closed degree-zero DG morphisms define the same morphism in the homotopy category exactly
when their difference is a coboundary. -/
@[simp]
theorem homOf_eq_iff {X Y : C} {f g : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    homOf R f hf = homOf R g hg ↔ f - g ∈ dgBoundaries R X Y :=
  dgHomotopyClass_eq_iff R hf hg

/-- Composition in the homotopy category is represented by DG composition. -/
@[simp]
theorem homOf_comp {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    homOf R f hf ≫ homOf R g hg =
      homOf R (dgCompZero R f g) (dgCompZero_mem_dgCycles R hf hg) :=
  dgHomotopyComp_dgHomotopyClass R f g hf hg

/-- If the DG composite of `f` and `g` is `k`, then the composite of their classes in the homotopy
category is the class of `k`. -/
theorem homOf_comp_eq_homOf_of_dgComp_eq {X Y Z : C} {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    {k : DGHom R 0 X Z} (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z)
    (hk : k ∈ dgCycles R X Z) (e : dgComp R f g (add_zero 0) = k) :
    homOf R f hf ≫ homOf R g hg = homOf R k hk := by
  subst e
  exact homOf_comp R f g hf hg

/-- If the DG composite of `f` and `g` is the identity, then so is the composite of their classes
in the homotopy category. -/
theorem homOf_comp_eq_id_of_dgComp_eq_dgId {X Y : C} {f : DGHom R 0 X Y} {g : DGHom R 0 Y X}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y X) (e : dgComp R f g (add_zero 0) = dgId R X) :
    homOf R f hf ≫ homOf R g hg = 𝟙 (of R X) :=
  (homOf_comp_eq_homOf_of_dgComp_eq R hf hg
    ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) e).trans (homOf_dgId R X)

/-- If the differential of a degree-minus-one morphism `k` is minus the composite of `f` and `g`,
then the composite of `f` and `g` vanishes in the homotopy category. -/
theorem homOf_comp_eq_zero_of_dgDifferential_eq_neg {X Y Z : C} {f : DGHom R 0 X Y}
    {g : DGHom R 0 Y Z} (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z)
    {k : DGHom R (-1) X Z} (hk : dgDifferential R (-1) k = -dgComp R f g (add_zero 0)) :
    homOf R f hf ≫ homOf R g hg = 0 := by
  rw [homOf_comp, homOf_eq_zero_iff, mem_dgBoundaries, dgCompZero_def]
  exact ⟨-k, by rw [map_neg, hk, neg_neg]⟩

/-- An object is a zero object of the homotopy category exactly when it is **contractible**: its
identity is the differential of a degree-minus-one endomorphism. -/
theorem isZero_of_iff_dgId_mem_dgBoundaries (X : C) :
    Limits.IsZero (of R X) ↔ dgId R X ∈ dgBoundaries R X X := by
  rw [Limits.IsZero.iff_id_eq_zero, ← homOf_dgId, homOf_eq_zero_iff]

end DGHomotopyCategory

end

end MathlibExt.DGSource
