/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationComplex
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarAssociatedGraded
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveFiltrationZeroImage
public import MathlibExt.Algebra.Algebra.NonUnitalIdeal.KSplit
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Ideal complexes and filtration-zero complexes

The ideal-to-kernel chain maps have the images
defining filtration zero. A ground-module
splitting of the ideal quotient gives tensor
component injectivity, and the image identities
give surjectivity. The resulting chain isomorphism
retains the positive bar’s zero augmentation
and arbitrary coefficient modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem originalIdealProjection_comp (s : I.KSplit) :
    (s.projection : A →ₗ[k] I.Algebra).comp
      (I.subtypeHom : I.Algebra →ₗ[k] A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change s.projection x.val = x
  exact s.projection_subtype x

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem originalIdealConsRetraction (s : I.KSplit) (n : ℕ) :
    (TensorPower.consLevelMap (s.projection : A →ₗ[k] I.Algebra) n).comp
      (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n) =
        LinearMap.id := by
  rw [TensorPower.consLevelMap_comp, originalIdealProjection_comp]
  change TensorPower.consLevelMap (LinearMap.id : I.Algebra →ₗ[k] I.Algebra) n =
    LinearMap.id
  exact TensorPower.consLevelMap_id n

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem originalIdealWordRetraction (s : I.KSplit) (n : ℕ) :
    (PiTensorProduct.map (fun _ : Fin n => (s.projection : A →ₗ[k] I.Algebra))).comp
      (PiTensorProduct.map (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A))) =
        LinearMap.id := by
  rw [← PiTensorProduct.map_comp]
  simp only [originalIdealProjection_comp]
  change PiTensorProduct.map (fun _ : Fin n => (LinearMap.id : I.Algebra →ₗ[k] I.Algebra)) =
    LinearMap.id
  exact PiTensorProduct.map_id

/-- The original ideal-to-kernel component has values in the exact original F0 stage. -/
def idealToNaiveFiltrationZeroComponent (n : ℕ) :
    (bComplex k I.Algebra).X n →ₗ[k] naiveWordFiltration k A I 0 n :=
  LinearMap.codRestrict (naiveWordFiltration k A I 0 n)
    ((idealToRelativeNaiveComplex k A I).f n).hom (fun x => by
      rw [naiveWordFiltration_zero_eq_range]
      exact ⟨x, rfl⟩)

theorem idealToNaiveFiltrationZeroComponent_val (n : ℕ)
    (x : (bComplex k I.Algebra).X n) :
    (naiveWordFiltration k A I 0 n).subtype
        (idealToNaiveFiltrationZeroComponent k A I n x) =
      ((idealToRelativeNaiveComplex k A I).f n).hom x := rfl

private theorem idealToNaiveFiltrationZeroComponent_comm (n : ℕ) :
    ModuleCat.ofHom (idealToNaiveFiltrationZeroComponent k A I (n + 1)) ≫
        (naiveFilteredWordComplex k A I 0).d (n + 1) n =
      (bComplex k I.Algebra).d (n + 1) n ≫
        ModuleCat.ofHom (idealToNaiveFiltrationZeroComponent k A I n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (naiveWordFiltration k A I 0 n).subtype
      (((naiveFilteredWordComplex k A I 0).d (n + 1) n).hom
        (idealToNaiveFiltrationZeroComponent k A I (n + 1) x)) =
    (naiveWordFiltration k A I 0 n).subtype
      (idealToNaiveFiltrationZeroComponent k A I n
        (((bComplex k I.Algebra).d (n + 1) n).hom x))
  rw [naiveFilteredWordComplex_d_val, idealToNaiveFiltrationZeroComponent_val]
  change ((relativeNaiveComplex k A I).d (n + 1) n).hom
      (((idealToRelativeNaiveComplex k A I).f (n + 1)).hom x) =
    ((idealToRelativeNaiveComplex k A I).f n).hom
      (((bComplex k I.Algebra).d (n + 1) n).hom x)
  have h := congrArg
    (fun f : (bComplex k I.Algebra).X (n + 1) ⟶
      (relativeNaiveComplex k A I).X n => f.hom x)
    ((idealToRelativeNaiveComplex k A I).comm (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The original ideal chain map factors through the original naive F0 complex. -/
def idealToNaiveFiltrationZeroComplex :
    bComplex k I.Algebra ⟶ naiveFilteredWordComplex k A I 0 :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (idealToNaiveFiltrationZeroComponent k A I n))
    (fun n => by exact idealToNaiveFiltrationZeroComponent_comm k A I n)

@[simp]
theorem idealToNaiveFiltrationZeroComplex_f (n : ℕ) :
    (idealToNaiveFiltrationZeroComplex k A I).f n =
      ModuleCat.ofHom (idealToNaiveFiltrationZeroComponent k A I n) := rfl

/-- Including the F0 factorization gives exactly the original ideal-to-kernel map. -/
theorem idealToNaiveFiltrationZeroComplex_inclusion :
    idealToNaiveFiltrationZeroComplex k A I ≫ naiveFilteredWordInclusion k A I 0 =
      idealToRelativeNaiveComplex k A I := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem originalIdealNaiveComponent_injective (s : I.KSplit) (n : ℕ) :
    Function.Injective ((idealToRelativeNaiveComplex k A I).f n).hom := by
  have hleft : Function.LeftInverse
      (TensorPower.consLevelMap (s.projection : A →ₗ[k] I.Algebra) n)
      (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n) := by
    intro x
    have h := congrArg (fun f => f x) (originalIdealConsRetraction k A I s n)
    change (TensorPower.consLevelMap (s.projection : A →ₗ[k] I.Algebra) n)
      ((TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n) x) = x at h
    exact h
  intro x y hxy
  apply hleft.injective
  have hincl := congrArg
    (fun f : bComplex k I.Algebra ⟶ bComplex k A => (f.f n).hom)
    (idealToRelativeNaiveComplex_ι k A I)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    cyclicBComplexHom_f, ModuleCat.hom_ofHom] at hincl
  have hx := congrArg (fun f => f x) hincl
  have hy := congrArg (fun f => f y) hincl
  have hkernel := congrArg
    (fun z => ((kernel.ι (cyclicBComplexHom I.quotientMap)).f n).hom z) hxy
  exact hx.symm.trans (hkernel.trans hy)

/-- The source k-splitting earns injectivity; the proved original image equality earns surjectivity. -/
theorem idealToNaiveFiltrationZeroComplex_bijective (s : I.KSplit) (n : ℕ) :
    Function.Bijective ((idealToNaiveFiltrationZeroComplex k A I).f n).hom := by
  change Function.Bijective (idealToNaiveFiltrationZeroComponent k A I n)
  constructor
  · intro x y hxy
    apply originalIdealNaiveComponent_injective k A I s n
    exact congrArg (fun z : naiveWordFiltration k A I 0 n => z.val) hxy
  · intro y
    have hy : y.val ∈ LinearMap.range ((idealToRelativeNaiveComplex k A I).f n).hom := by
      rw [← naiveWordFiltration_zero_eq_range]
      exact y.property
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- Degreewise bijectivity of the original factorization earns its native IsIso. -/
theorem idealToNaiveFiltrationZeroComplex_isIso (s : I.KSplit) :
    IsIso (idealToNaiveFiltrationZeroComplex k A I) := by
  let : ∀ n : ℕ, IsIso ((idealToNaiveFiltrationZeroComplex k A I).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (idealToNaiveFiltrationZeroComplex_bijective k A I s n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Under the original k-split extension, the ideal b complex is the original F0 complex. -/
def naiveFiltrationZeroIdealIso (s : I.KSplit) :
    bComplex k I.Algebra ≅ naiveFilteredWordComplex k A I 0 := by
  letI := idealToNaiveFiltrationZeroComplex_isIso k A I s
  exact asIso (idealToNaiveFiltrationZeroComplex k A I)

@[simp]
theorem naiveFiltrationZeroIdealIso_hom (s : I.KSplit) :
    (naiveFiltrationZeroIdealIso k A I s).hom = idealToNaiveFiltrationZeroComplex k A I := rfl

/-- The isomorphism's original forward map recovers exactly the original ideal-to-kernel lift. -/
theorem naiveFiltrationZeroIdealIso_hom_inclusion (s : I.KSplit) :
    (naiveFiltrationZeroIdealIso k A I s).hom ≫ naiveFilteredWordInclusion k A I 0 =
      idealToRelativeNaiveComplex k A I := by
  rw [naiveFiltrationZeroIdealIso_hom]
  exact idealToNaiveFiltrationZeroComplex_inclusion k A I

/-- The original forward map retains the ideal inclusion in every original word coordinate. -/
theorem naiveFiltrationZeroIdealIso_hom_word (s : I.KSplit) (n : ℕ) :
    (relativeNaiveWordMap k A I n).comp
        (((naiveFiltrationZeroIdealIso k A I s).hom ≫
          naiveFilteredWordInclusion k A I 0).f n).hom =
      (PiTensorProduct.map
        (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))).comp
          (TensorPower.consEquiv k I.Algebra n).toLinearMap := by
  rw [naiveFiltrationZeroIdealIso_hom_inclusion]
  exact relativeNaiveWordMap_idealToRelative k A I n

/-- The native inverse has the source projection as its original ideal-word coordinates. -/
theorem naiveFiltrationZeroIdealIso_inv_word (s : I.KSplit) (n : ℕ)
    (y : naiveWordFiltration k A I 0 n) :
    TensorPower.consEquiv k I.Algebra n
        (((naiveFiltrationZeroIdealIso k A I s).inv.f n).hom y) =
      PiTensorProduct.map
        (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra))
          (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I 0 n).subtype y)) := by
  let e := naiveFiltrationZeroIdealIso k A I s
  let x : (bComplex k I.Algebra).X n := (e.inv.f n).hom y
  have hx : idealToNaiveFiltrationZeroComponent k A I n x = y := by
    have h := congrArg
      (fun f : naiveFilteredWordComplex k A I 0 ⟶
        naiveFilteredWordComplex k A I 0 => (f.f n).hom y) e.inv_hom_id
    change idealToNaiveFiltrationZeroComponent k A I n
      (((e.inv.f n).hom y)) = y at h
    exact h
  have hr := congrArg
    (fun f => f (TensorPower.consEquiv k I.Algebra n x))
    (originalIdealWordRetraction k A I s (n + 1))
  change PiTensorProduct.map
    (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra))
    (PiTensorProduct.map
      (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))
      (TensorPower.consEquiv k I.Algebra n x)) =
      TensorPower.consEquiv k I.Algebra n x at hr
  have hw := congrArg (fun f => f x) (relativeNaiveWordMap_idealToRelative k A I n)
  change relativeNaiveWordMap k A I n
      (((idealToRelativeNaiveComplex k A I).f n).hom x) =
    PiTensorProduct.map
      (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))
      (TensorPower.consEquiv k I.Algebra n x) at hw
  change TensorPower.consEquiv k I.Algebra n x = _
  rw [← hx, idealToNaiveFiltrationZeroComponent_val, hw]
  exact hr.symm

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- The original positive ideal-to-kernel component has values in the exact full original F0 stage. -/
def idealToPositiveFiltrationZeroComponent (n : ℕ) :
    (positiveBarComplex k I.Algebra V).X n →ₗ[k] barFullWordFiltration k A I V 0 n :=
  LinearMap.codRestrict (barFullWordFiltration k A I V 0 n)
    ((idealToRelativePositiveBarComplex k A I V).f n).hom (fun x => by
      cases n with
      | zero =>
          change ((idealToRelativePositiveBarComplex k A I V).f 0).hom x = 0
          rw [idealToRelativePositiveBarComplex_f_zero]
          rfl
      | succ n =>
          change ((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom x ∈
            barWordFiltration k A I V 0 n
          rw [barWordFiltration_zero_eq_range]
          exact ⟨x, rfl⟩)

theorem idealToPositiveFiltrationZeroComponent_val (n : ℕ)
    (x : (positiveBarComplex k I.Algebra V).X n) :
    (barFullWordFiltration k A I V 0 n).subtype
        (idealToPositiveFiltrationZeroComponent k A I V n x) =
      ((idealToRelativePositiveBarComplex k A I V).f n).hom x := rfl

private theorem idealToPositiveFiltrationZeroComponent_comm (n : ℕ) :
    ModuleCat.ofHom (idealToPositiveFiltrationZeroComponent k A I V (n + 1)) ≫
        (barFilteredWordComplex k A I V 0).d (n + 1) n =
      (positiveBarComplex k I.Algebra V).d (n + 1) n ≫
        ModuleCat.ofHom (idealToPositiveFiltrationZeroComponent k A I V n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (barFullWordFiltration k A I V 0 n).subtype
      (((barFilteredWordComplex k A I V 0).d (n + 1) n).hom
        (idealToPositiveFiltrationZeroComponent k A I V (n + 1) x)) =
    (barFullWordFiltration k A I V 0 n).subtype
      (idealToPositiveFiltrationZeroComponent k A I V n
        (((positiveBarComplex k I.Algebra V).d (n + 1) n).hom x))
  rw [barFilteredWordComplex_d_val, idealToPositiveFiltrationZeroComponent_val]
  change ((relativePositiveBarComplex k A I V).d (n + 1) n).hom
      (((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom x) =
    ((idealToRelativePositiveBarComplex k A I V).f n).hom
      (((positiveBarComplex k I.Algebra V).d (n + 1) n).hom x)
  have h := congrArg
    (fun f : (positiveBarComplex k I.Algebra V).X (n + 1) ⟶
      (relativePositiveBarComplex k A I V).X n => f.hom x)
    ((idealToRelativePositiveBarComplex k A I V).comm (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The arbitrary-coefficient positive ideal chain map factors through its original F0 complex. -/
def idealToPositiveFiltrationZeroComplex :
    positiveBarComplex k I.Algebra V ⟶ barFilteredWordComplex k A I V 0 :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (idealToPositiveFiltrationZeroComponent k A I V n))
    (fun n => by exact idealToPositiveFiltrationZeroComponent_comm k A I V n)

@[simp]
theorem idealToPositiveFiltrationZeroComplex_f (n : ℕ) :
    (idealToPositiveFiltrationZeroComplex k A I V).f n =
      ModuleCat.ofHom (idealToPositiveFiltrationZeroComponent k A I V n) := rfl

/-- Including the full F0 factorization gives exactly the original positive ideal-to-kernel map. -/
theorem idealToPositiveFiltrationZeroComplex_inclusion :
    idealToPositiveFiltrationZeroComplex k A I V ≫ barFilteredWordInclusion k A I V 0 =
      idealToRelativePositiveBarComplex k A I V := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem originalIdealCoefficientWordRetraction (s : I.KSplit) (n : ℕ) :
    (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
      (PiTensorProduct.map
        (fun _ : Fin n => (s.projection : A →ₗ[k] I.Algebra)))).comp
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map
          (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A)))) =
      LinearMap.id := by
  rw [← TensorProduct.map_comp, LinearMap.id_comp, originalIdealWordRetraction]
  change TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (LinearMap.id : TensorPower k n I.Algebra →ₗ[k] TensorPower k n I.Algebra) =
      LinearMap.id
  exact TensorProduct.map_id

private theorem originalIdealPositiveComponent_injective (s : I.KSplit) (n : ℕ) :
    Function.Injective ((idealToRelativePositiveBarComplex k A I V).f n).hom := by
  cases n with
  | zero =>
      let : Subsingleton ((positiveBarComplex k I.Algebra V).X 0) :=
        (ModuleCat.isZero_iff_subsingleton).mp (positiveBarComplex_isZero_zero k I.Algebra V)
      intro x y _h
      exact Subsingleton.elim x y
  | succ n =>
      have hleft : Function.LeftInverse
          (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            (PiTensorProduct.map
              (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra))))
          (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            (PiTensorProduct.map
              (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))) := by
        intro x
        have h := congrArg (fun f => f x) (originalIdealCoefficientWordRetraction k A I V s (n + 1))
        change (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (PiTensorProduct.map
            (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra))))
          ((TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            (PiTensorProduct.map
              (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))) x) = x at h
        exact h
      intro x y hxy
      apply (positiveBarWordIso k I.Algebra V n).toLinearEquiv.injective
      apply hleft.injective
      have h := congrArg (relativePositiveBarWordMap k A I V n) hxy
      rw [relativePositiveBarWordMap_idealToRelative_apply,
        relativePositiveBarWordMap_idealToRelative_apply] at h
      exact h

/-- The original source k-splitting and image equality earn full component bijectivity. -/
theorem idealToPositiveFiltrationZeroComplex_bijective (s : I.KSplit) (n : ℕ) :
    Function.Bijective ((idealToPositiveFiltrationZeroComplex k A I V).f n).hom := by
  change Function.Bijective (idealToPositiveFiltrationZeroComponent k A I V n)
  constructor
  · intro x y hxy
    apply originalIdealPositiveComponent_injective k A I V s n
    exact congrArg (fun z : barFullWordFiltration k A I V 0 n => z.val) hxy
  · cases n with
    | zero =>
        intro y
        have hy : y = 0 := by
          apply Subtype.ext
          simpa only [barFullWordFiltration, Submodule.mem_bot, ZeroMemClass.coe_zero] using
            y.property
        refine ⟨0, ?_⟩
        rw [map_zero, hy]
    | succ n =>
        intro y
        have hy : y.val ∈
            LinearMap.range ((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom := by
          rw [← barWordFiltration_zero_eq_range]
          exact y.property
        rcases hy with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply Subtype.ext
        exact hx

/-- The positive ideal-to-F0 chain map is a native isomorphism under the original source splitting. -/
theorem idealToPositiveFiltrationZeroComplex_isIso (s : I.KSplit) :
    IsIso (idealToPositiveFiltrationZeroComplex k A I V) := by
  let : ∀ n : ℕ, IsIso ((idealToPositiveFiltrationZeroComplex k A I V).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (idealToPositiveFiltrationZeroComplex_bijective k A I V s n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The source k-split ideal extension identifies the positive ideal bar with the original F0 complex. -/
def positiveFiltrationZeroIdealIso (s : I.KSplit) :
    positiveBarComplex k I.Algebra V ≅ barFilteredWordComplex k A I V 0 := by
  letI := idealToPositiveFiltrationZeroComplex_isIso k A I V s
  exact asIso (idealToPositiveFiltrationZeroComplex k A I V)

@[simp]
theorem positiveFiltrationZeroIdealIso_hom (s : I.KSplit) :
    (positiveFiltrationZeroIdealIso k A I V s).hom =
      idealToPositiveFiltrationZeroComplex k A I V := rfl

/-- The original forward isomorphism recovers exactly the original positive ideal-to-kernel lift. -/
theorem positiveFiltrationZeroIdealIso_hom_inclusion (s : I.KSplit) :
    (positiveFiltrationZeroIdealIso k A I V s).hom ≫ barFilteredWordInclusion k A I V 0 =
      idealToRelativePositiveBarComplex k A I V := by
  rw [positiveFiltrationZeroIdealIso_hom]
  exact idealToPositiveFiltrationZeroComplex_inclusion k A I V

/-- Positive forward coordinates retain the coefficient identity and every original ideal inclusion. -/
theorem positiveFiltrationZeroIdealIso_hom_word (s : I.KSplit) (n : ℕ) :
    (relativePositiveBarWordMap k A I V n).comp
        (((positiveFiltrationZeroIdealIso k A I V s).hom ≫
          barFilteredWordInclusion k A I V 0).f (n + 1)).hom =
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map
          (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))).comp
            (positiveBarWordIso k I.Algebra V n).hom.hom := by
  rw [positiveFiltrationZeroIdealIso_hom_inclusion]
  exact relativePositiveBarWordMap_idealToRelative k A I V n

/-- The positive inverse has the original identity-coefficient ideal-projection coordinates. -/
theorem positiveFiltrationZeroIdealIso_inv_word (s : I.KSplit) (n : ℕ)
    (y : barWordFiltration k A I V 0 n) :
    (positiveBarWordIso k I.Algebra V n).hom.hom
        (((positiveFiltrationZeroIdealIso k A I V s).inv.f (n + 1)).hom y) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map
          (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra)))
          (relativePositiveBarWordMap k A I V n
            ((barWordFiltration k A I V 0 n).subtype y)) := by
  let e := positiveFiltrationZeroIdealIso k A I V s
  let x : (positiveBarComplex k I.Algebra V).X (n + 1) := (e.inv.f (n + 1)).hom y
  have hx : idealToPositiveFiltrationZeroComponent k A I V (n + 1) x = y := by
    have h := congrArg
      (fun f : barFilteredWordComplex k A I V 0 ⟶
        barFilteredWordComplex k A I V 0 => (f.f (n + 1)).hom y) e.inv_hom_id
    change idealToPositiveFiltrationZeroComponent k A I V (n + 1)
      (((e.inv.f (n + 1)).hom y)) = y at h
    exact h
  have hr := congrArg
    (fun f => f ((positiveBarWordIso k I.Algebra V n).hom.hom x))
    (originalIdealCoefficientWordRetraction k A I V s (n + 1))
  change TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (PiTensorProduct.map
      (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra)))
    (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
      (PiTensorProduct.map
        (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))
      ((positiveBarWordIso k I.Algebra V n).hom.hom x)) =
      (positiveBarWordIso k I.Algebra V n).hom.hom x at hr
  have hw := relativePositiveBarWordMap_idealToRelative_apply k A I V n x
  change (positiveBarWordIso k I.Algebra V n).hom.hom x = _
  rw [← hx]
  change (positiveBarWordIso k I.Algebra V n).hom.hom x =
    TensorProduct.map (LinearMap.id : V →ₗ[k] V)
      (PiTensorProduct.map
        (fun _ : Fin (n + 1) => (s.projection : A →ₗ[k] I.Algebra)))
      (relativePositiveBarWordMap k A I V n
        ((barFullWordFiltration k A I V 0 (n + 1)).subtype
          (idealToPositiveFiltrationZeroComponent k A I V (n + 1) x)))
  rw [idealToPositiveFiltrationZeroComponent_val, hw]
  exact hr.symm

/-- The positive forward isomorphism retains the original zero augmentation component. -/
theorem positiveFiltrationZeroIdealIso_hom_f_zero (s : I.KSplit) :
    (positiveFiltrationZeroIdealIso k A I V s).hom.f 0 = 0 :=
  (positiveBarComplex_isZero_zero k I.Algebra V).eq_of_src _ _

/-- The original F0 target has its bottom augmentation, with no supplied zero-object premise. -/
theorem positiveFiltrationZero_isZero_zero :
    IsZero ((barFilteredWordComplex k A I V 0).X 0) := by
  apply (ModuleCat.isZero_iff_subsingleton).mpr
  change Subsingleton (⊥ : Submodule k ((relativePositiveBarComplex k A I V).X 0))
  infer_instance

end ModuleCat.Algebra.Hochschild.NonUnital
