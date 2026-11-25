/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ParameterMap
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tor boundaries in either coefficient

Tensor right exactness gives preservation of finite colimits and identifies
the degree-zero derived functor with tensor product. The split projective
horseshoe gives the Tor long exact sequence and its degree-zero quotient
endpoint. Connecting-map naturality retains both module maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v
variable (R : Type u) [CommRing R]

/-- The actual larger-universe tensor functor is right exact. -/
theorem nativeTensorLeft_preservesFiniteColimits (M : ModuleCat.{max u v} R) :
    PreservesFiniteColimits ((tensoringLeft (ModuleCat.{max u v} R)).obj M) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2
  intro S hS
  have hg : Function.Surjective S.g :=
    (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  constructor
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact lTensor_exact M
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) hg
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective M hg

/-- The canonical native degree-zero comparison has the literal tensor carrier. -/
def nativeTorZeroIso (M N : ModuleCat.{max u v} R) :
    (((Tor (ModuleCat.{max u v} R) 0).obj M).obj N) ≅
      ModuleCat.of R (M ⊗[R] N) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  letI : PreservesFiniteColimits F := nativeTensorLeft_preservesFiniteColimits R M
  exact F.leftDerivedZeroIsoSelf.app N

/-- The native degree-zero comparison retains the actual resolved-coefficient map. -/
@[reassoc]
theorem nativeTorZeroIso_hom_naturality_resolved (M : ModuleCat.{max u v} R)
    {N N' : ModuleCat.{max u v} R} (f : N ⟶ N') :
    ((Tor (ModuleCat.{max u v} R) 0).obj M).map f ≫
        (nativeTorZeroIso R M N').hom =
      (nativeTorZeroIso R M N).hom ≫ ModuleCat.ofHom (f.hom.lTensor M) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  let : PreservesFiniteColimits F := nativeTensorLeft_preservesFiniteColimits R M
  exact F.leftDerivedZeroIsoSelf.hom.naturality f

/-- The original native Tor boundary is the canonical horseshoe homology boundary. -/
def nativeTorConnecting (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).obj S.X₃) ⟶
      (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) :=
  LeftDerivedDelta.LDdelta ((tensoringLeft (ModuleCat.{max u v} R)).obj M) q S hS

/-- Five consecutive original native Tor maps, including the actual boundary. -/
def nativeTorLongExactWindow (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ComposableArrows (ModuleCat.{max u v} R) 5 :=
  ComposableArrows.mk₅
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).map S.f)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).map S.g)
    (nativeTorConnecting R M S hS q)
    (((Tor (ModuleCat.{max u v} R) q).obj M).map S.f)
    (((Tor (ModuleCat.{max u v} R) q).obj M).map S.g)

/-- The actual short exact coefficient sequence earns the native Tor exact window. -/
theorem nativeTorLongExactWindow_exact (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (nativeTorLongExactWindow R M S hS q).Exact :=
  LeftDerivedDelta.LDlongSequence_exact
    ((tensoringLeft (ModuleCat.{max u v} R)).obj M) q S hS

/-- The literal degree-zero native quotient map is epi. -/
theorem nativeTor_epi_zero (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) :
    Epi (((Tor (ModuleCat.{max u v} R) 0).obj M).map S.g) :=
  LeftDerivedDelta.LDepi_zero ((tensoringLeft (ModuleCat.{max u v} R)).obj M) S hS

/-- Native boundaries retain every actual map of original short exact sequences. -/
@[reassoc]
theorem nativeTorConnecting_naturality_sequence (M : ModuleCat.{max u v} R)
    {S S' : ShortComplex (ModuleCat.{max u v} R)} (f : S ⟶ S')
    (hS : S.ShortExact) (hS' : S'.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).map f.τ₃ ≫
        nativeTorConnecting R M S' hS' q =
      nativeTorConnecting R M S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).obj M).map f.τ₁ :=
  LeftDerivedDelta.LDdelta_natural
    ((tensoringLeft (ModuleCat.{max u v} R)).obj M) q S' S f hS' hS

/-- Native boundaries retain the actual map in the other original coefficient. -/
@[reassoc]
theorem nativeTorConnecting_naturality_coefficient
    {M M' : ModuleCat.{max u v} R} (f : M ⟶ M')
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).map f).app S.X₃ ≫
        nativeTorConnecting R M' S hS q =
      nativeTorConnecting R M S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).map f).app S.X₁ :=
  LeftDerivedDelta.LDdelta_natural_functor
    ((tensoringLeft (ModuleCat.{max u v} R)).map f) q S hS

/-- The actual boundary is an isomorphism when its neighboring original maps vanish. -/
theorem nativeTorConnecting_isIso (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ)
    (h₂ : IsZero (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).obj S.X₂))
    (hf : ((Tor (ModuleCat.{max u v} R) q).obj M).map S.f = 0) :
    IsIso (nativeTorConnecting R M S hS q) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  change IsIso (LeftDerivedDelta.LDdelta F q S hS)
  let δ := LeftDerivedDelta.LDdelta F q S hS
  have h₂' : IsZero ((F.leftDerived (q + 1)).obj S.X₂) := h₂
  have hf' : (F.leftDerived q).map S.f = 0 := hf
  obtain ⟨wC, hC⟩ := LeftDerivedDelta.LDexact_C F q S hS
  obtain ⟨wA, hA⟩ := LeftDerivedDelta.LDexact_A F q S hS
  let C : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk ((F.leftDerived (q + 1)).map S.g) δ wC
  let A : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk δ ((F.leftDerived q).map S.f) wA
  have hg : (F.leftDerived (q + 1)).map S.g = 0 := h₂'.eq_of_src _ _
  have : Mono C.g := (C.exact_iff_mono hg).mp hC
  have : Epi A.f := (A.exact_iff_epi hf').mp hA
  change IsIso δ
  exact isIso_of_mono_of_epi _

/-- Canonical native symmetry transports the original boundary to the first coefficient. -/
def nativeTorConnectingFirst (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj S.X₃).obj N) ⟶
      (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N) :=
  (nativeTorSymmetry R N S.X₃ (q + 1)).inv ≫ nativeTorConnecting R N S hS q ≫
    (nativeTorSymmetry R N S.X₁ q).hom

/-- The first-variable window retains all five original native Tor maps. -/
def nativeTorLongExactWindowFirst (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ComposableArrows (ModuleCat.{max u v} R) 5 :=
  ComposableArrows.mk₅
    (((Tor (ModuleCat.{max u v} R) (q + 1)).map S.f).app N)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).map S.g).app N)
    (nativeTorConnectingFirst R N S hS q)
    (((Tor (ModuleCat.{max u v} R) q).map S.f).app N)
    (((Tor (ModuleCat.{max u v} R) q).map S.g).app N)

/-- Canonical native symmetry compares the complete original first-variable exact window. -/
private def nativeTorLongExactWindowFirstIso (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    nativeTorLongExactWindowFirst R N S hS q ≅ nativeTorLongExactWindow R N S hS q := by
  let E₁ := ((nativeTorSymmetryNatIso R (q + 1)).app N).symm
  let E₀ := ((nativeTorSymmetryNatIso R q).app N).symm
  refine ComposableArrows.isoMk₅
    (E₁.app S.X₁) (E₁.app S.X₂) (E₁.app S.X₃)
    (E₀.app S.X₁) (E₀.app S.X₂) (E₀.app S.X₃) ?_ ?_ ?_ ?_ ?_
  · exact E₁.hom.naturality S.f
  · exact E₁.hom.naturality S.g
  · change (E₁.app S.X₃).hom ≫ nativeTorConnecting R N S hS q ≫
        (E₀.app S.X₁).inv ≫ (E₀.app S.X₁).hom =
      (E₁.app S.X₃).hom ≫ nativeTorConnecting R N S hS q
    simp only [Iso.inv_hom_id, Category.comp_id]
  · exact E₀.hom.naturality S.f
  · exact E₀.hom.naturality S.g

/-- The actual first-variable native Tor window is exact. -/
theorem nativeTorLongExactWindowFirst_exact (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (nativeTorLongExactWindowFirst R N S hS q).Exact :=
  ComposableArrows.exact_of_iso (nativeTorLongExactWindowFirstIso R N S hS q).symm
    (nativeTorLongExactWindow_exact R N S hS q)

/-- The actual first-variable degree-zero quotient endpoint is epi. -/
theorem nativeTor_epi_zero_first (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) :
    Epi (((Tor (ModuleCat.{max u v} R) 0).map S.g).app N) := by
  have : Epi (((Tor (ModuleCat.{max u v} R) 0).obj N).map S.g) :=
    nativeTor_epi_zero R N S hS
  let E := ((nativeTorSymmetryNatIso R 0).app N).symm
  let e : Arrow.mk (((Tor (ModuleCat.{max u v} R) 0).map S.g).app N) ≅
      Arrow.mk (((Tor (ModuleCat.{max u v} R) 0).obj N).map S.g) :=
    Arrow.isoMk (E.app S.X₂) (E.app S.X₃) (E.hom.naturality S.g).symm
  exact ((MorphismProperty.epimorphisms (ModuleCat.{max u v} R)).arrow_mk_iso_iff e).mpr
    (MorphismProperty.epimorphisms.infer_property _)

/-- The first-variable boundary retains actual maps of the original short exact sequence. -/
@[reassoc]
theorem nativeTorConnectingFirst_naturality_sequence (N : ModuleCat.{max u v} R)
    {S S' : ShortComplex (ModuleCat.{max u v} R)} (f : S ⟶ S')
    (hS : S.ShortExact) (hS' : S'.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).map f.τ₃).app N ≫
        nativeTorConnectingFirst R N S' hS' q =
      nativeTorConnectingFirst R N S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).map f.τ₁).app N := by
  let E₁ := ((nativeTorSymmetryNatIso R (q + 1)).app N).symm
  let E₀ := ((nativeTorSymmetryNatIso R q).app N).symm
  have hδ := (nativeTorConnecting_naturality_sequence R N f hS hS' q).symm
  have h := Iso.conjugate_naturality (E₁.app S'.X₃) (E₁.app S.X₃)
    (E₀.app S'.X₁) (E₀.app S.X₁)
    (nativeTorConnecting R N S' hS' q) (nativeTorConnecting R N S hS q)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).map f.τ₃).app N)
    (((Tor (ModuleCat.{max u v} R) q).map f.τ₁).app N)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj N).map f.τ₃)
    (((Tor (ModuleCat.{max u v} R) q).obj N).map f.τ₁)
    (E₁.hom.naturality f.τ₃) (E₀.inv.naturality f.τ₁) hδ
  exact h.symm

private theorem nativeTorSymmetry_parameter_hom
    {N N' : ModuleCat.{max u v} R} (g : N ⟶ N') (X : ModuleCat.{max u v} R) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) q).map g).app X ≫ (nativeTorSymmetry R N' X q).hom =
      (nativeTorSymmetry R N X q).hom ≫ ((Tor (ModuleCat.{max u v} R) q).obj X).map g := by
  let T := Tor (ModuleCat.{max u v} R) q
  let E := nativeTorSymmetryNatIso R q
  exact congrArg (fun a : T.obj N ⟶ T.flip.obj N' => a.app X) (E.hom.naturality g)

private theorem nativeTorSymmetry_parameter_inv
    {N N' : ModuleCat.{max u v} R} (g : N ⟶ N') (X : ModuleCat.{max u v} R) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) q).obj X).map g ≫ (nativeTorSymmetry R N' X q).inv =
      (nativeTorSymmetry R N X q).inv ≫ ((Tor (ModuleCat.{max u v} R) q).map g).app X := by
  let T := Tor (ModuleCat.{max u v} R) q
  let E := nativeTorSymmetryNatIso R q
  exact congrArg (fun a : T.flip.obj N ⟶ T.obj N' => a.app X) (E.inv.naturality g)

/-- The first-variable boundary also retains the map in the other original coefficient. -/
@[reassoc]
theorem nativeTorConnectingFirst_naturality_coefficient
    {N N' : ModuleCat.{max u v} R} (g : N ⟶ N')
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).obj S.X₃).map g ≫
        nativeTorConnectingFirst R N' S hS q =
      nativeTorConnectingFirst R N S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).obj S.X₁).map g := by
  let T₁ := Tor (ModuleCat.{max u v} R) (q + 1)
  let T₀ := Tor (ModuleCat.{max u v} R) q
  have hs := nativeTorSymmetry_parameter_inv R g S.X₃ (q + 1)
  have ht := nativeTorSymmetry_parameter_hom R g S.X₁ q
  have hδ := (nativeTorConnecting_naturality_coefficient R g S hS q).symm
  have h := Iso.conjugate_naturality
    (nativeTorSymmetry R N' S.X₃ (q + 1)).symm
    (nativeTorSymmetry R N S.X₃ (q + 1)).symm
    (nativeTorSymmetry R N' S.X₁ q).symm (nativeTorSymmetry R N S.X₁ q).symm
    (nativeTorConnecting R N' S hS q) (nativeTorConnecting R N S hS q)
    ((T₁.obj S.X₃).map g) ((T₀.obj S.X₁).map g)
    ((T₁.map g).app S.X₃) ((T₀.map g).app S.X₁) hs ht hδ
  exact h.symm

end ModuleCat.UniverseTensor
