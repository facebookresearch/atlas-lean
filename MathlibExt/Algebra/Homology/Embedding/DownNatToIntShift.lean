/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToInt
public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntExact
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology
public import MathlibExt.Algebra.Homology.Embedding.ExtendHomotopy
public import MathlibExt.Algebra.Homology.Embedding.SupportedRestrictionExtension

/-!
# Zero extension above a specified integer lower bound

For an integer b, the embedding n ↦ b + n extends nonnegative chain
complexes by zero below b. Restriction and extension reconstruct an integer
complex whose terms below b are zero. The corresponding homology, exactness
and homotopy comparisons are natural.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape

/-- The embedding of downward complex shapes sending `n : ℕ` to
`b + n : ℤ`. It is the opposite-shape form of Mathlib's
`embeddingUpIntGE`. -/
def embeddingDownNatToIntShift (b : ℤ) :
    Embedding (down ℕ) (down ℤ) :=
  (embeddingUpIntGE b).op

@[simp]
theorem embeddingDownNatToIntShift_f (b : ℤ) (n : ℕ) :
    (embeddingDownNatToIntShift b).f n = b + n :=
  rfl

instance (b : ℤ) : (embeddingDownNatToIntShift b).IsRelIff where
  rel' i j h := by
    change b + (j : ℤ) + 1 = b + (i : ℤ) at h
    change j + 1 = i
    omega

instance (b : ℤ) : (embeddingDownNatToIntShift b).IsTruncLE where
  mem_prev {i j} h := by
    refine ⟨j + 1, ?_⟩
    change b + (j : ℤ) + 1 = i at h
    change b + ((j + 1 : ℕ) : ℤ) = i
    omega

/-- An integer lies outside the shifted nonnegative range exactly when it is
strictly below the supplied lower bound. -/
theorem notMem_range_embeddingDownNatToIntShift_iff (b z : ℤ) :
    (∀ n : ℕ, (embeddingDownNatToIntShift b).f n ≠ z) ↔ z < b := by
  simpa [embeddingDownNatToIntShift] using
    (notMem_range_embeddingUpIntGE_iff b z)

end ComplexShape

namespace ComplexShape

section RestrictionFunctor

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Restriction of an integer chain complex to degrees `b + n`. -/
def embeddingDownNatToIntShiftRestrictionFunctor (b : ℤ) :
    ChainComplex C ℤ ⥤ ChainComplex C ℕ :=
  (embeddingDownNatToIntShift b).restrictionFunctor C

end RestrictionFunctor

section ExtendFunctor

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [HasZeroMorphisms C]

/-- Zero extension from nonnegative degrees to integer degrees starting at
`b`. -/
noncomputable def embeddingDownNatToIntShiftExtendFunctor (b : ℤ) :
    ChainComplex C ℕ ⥤ ChainComplex C ℤ :=
  (embeddingDownNatToIntShift b).extendFunctor C

end ExtendFunctor

end ComplexShape

namespace HomologicalComplex

section Components

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

@[simp]
theorem restriction_embeddingDownNatToIntShift_X
    (K : ChainComplex C ℤ) (b : ℤ) (n : ℕ) :
    (K.restriction (ComplexShape.embeddingDownNatToIntShift b)).X n =
      K.X (b + n) :=
  rfl

@[simp]
theorem restriction_embeddingDownNatToIntShift_d
    (K : ChainComplex C ℤ) (b : ℤ) (n : ℕ) :
    (K.restriction (ComplexShape.embeddingDownNatToIntShift b)).d
        (n + 1) n =
      K.d (b + ((n + 1 : ℕ) : ℤ)) (b + n) :=
  rfl

variable [HasZeroObject C]

/-- The component isomorphism for a shifted zero extension on its range. -/
noncomputable def extendDownNatToIntShiftXIso
    (K : ChainComplex C ℕ) (b : ℤ) (n : ℕ) :
    (K.extend (ComplexShape.embeddingDownNatToIntShift b)).X (b + n) ≅
      K.X n :=
  K.extendXIso (ComplexShape.embeddingDownNatToIntShift b) rfl

/-- The differential of a shifted zero extension, in the native component
coordinates. -/
theorem extendDownNatToIntShift_d
    (K : ChainComplex C ℕ) (b : ℤ) (n : ℕ) :
    (K.extend (ComplexShape.embeddingDownNatToIntShift b)).d
        (b + ((n + 1 : ℕ) : ℤ)) (b + n) =
      (extendDownNatToIntShiftXIso K b (n + 1)).hom ≫
        K.d (n + 1) n ≫
          (extendDownNatToIntShiftXIso K b n).inv :=
  K.extend_d_eq (ComplexShape.embeddingDownNatToIntShift b) rfl rfl

/-- A shifted zero extension is zero strictly below its lower bound. -/
theorem isZero_extendDownNatToIntShift_X_lt
    (K : ChainComplex C ℕ) (b z : ℤ) (hz : z < b) :
    IsZero ((K.extend
      (ComplexShape.embeddingDownNatToIntShift b)).X z) :=
  K.isZero_extend_X (ComplexShape.embeddingDownNatToIntShift b) z
    ((ComplexShape.notMem_range_embeddingDownNatToIntShift_iff b z).2 hz)

end Components

section Reconstruction

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A complex whose terms below `b` are zero is strictly supported on the
shifted nonnegative range. -/
theorem isStrictlySupported_embeddingDownNatToIntShift
    (K : ChainComplex C ℤ) (b : ℤ)
    (hb : ∀ i : ℤ, i < b → IsZero (K.X i)) :
    K.IsStrictlySupported (ComplexShape.embeddingDownNatToIntShift b) where
  isZero i hi := hb i
    ((ComplexShape.notMem_range_embeddingDownNatToIntShift_iff b i).1 hi)

variable [HasZeroObject C]

/-- Restriction to `b + ℕ`, followed by zero extension, reconstructs an
integer complex whose terms below `b` are zero. The construction specializes
the generic strictly-supported restriction/extension comparison. -/
noncomputable def restrictExtendDownNatToIntShiftIso
    (K : ChainComplex C ℤ) (b : ℤ)
    (hb : ∀ i : ℤ, i < b → IsZero (K.X i)) :
    (K.restriction (ComplexShape.embeddingDownNatToIntShift b)).extend
        (ComplexShape.embeddingDownNatToIntShift b) ≅ K := by
  let e := ComplexShape.embeddingDownNatToIntShift b
  let _ : K.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift K b hb
  change K.stupidTrunc e ≅ K
  exact K.restrictExtendIsoOfIsStrictlySupported e

/-- The forward shifted reconstruction component at every range degree. -/
@[simp]
theorem restrictExtendDownNatToIntShiftIso_hom_f
    (K : ChainComplex C ℤ) (b : ℤ)
    (hb : ∀ i : ℤ, i < b → IsZero (K.X i)) (n : ℕ) :
    (restrictExtendDownNatToIntShiftIso K b hb).hom.f (b + n) =
      (K.stupidTruncXIso
        (ComplexShape.embeddingDownNatToIntShift b) rfl).hom := by
  let e := ComplexShape.embeddingDownNatToIntShift b
  let _ : K.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift K b hb
  change (K.restrictExtendIsoOfIsStrictlySupported e).hom.f (e.f n) = _
  exact K.restrictExtendIsoOfIsStrictlySupported_hom_f e rfl

/-- The inverse shifted reconstruction component at every range degree. -/
@[simp]
theorem restrictExtendDownNatToIntShiftIso_inv_f
    (K : ChainComplex C ℤ) (b : ℤ)
    (hb : ∀ i : ℤ, i < b → IsZero (K.X i)) (n : ℕ) :
    (restrictExtendDownNatToIntShiftIso K b hb).inv.f (b + n) =
      (K.stupidTruncXIso
        (ComplexShape.embeddingDownNatToIntShift b) rfl).inv := by
  let e := ComplexShape.embeddingDownNatToIntShift b
  let _ : K.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift K b hb
  change (K.restrictExtendIsoOfIsStrictlySupported e).inv.f (e.f n) = _
  exact K.restrictExtendIsoOfIsStrictlySupported_inv_f e rfl

/-- The forward shifted reconstruction is natural in maps of complexes that
are zero below the same bound. -/
@[reassoc]
theorem restrictExtendDownNatToIntShiftIso_hom_naturality
    {K L : ChainComplex C ℤ} (φ : K ⟶ L) (b : ℤ)
    (hK : ∀ i : ℤ, i < b → IsZero (K.X i))
    (hL : ∀ i : ℤ, i < b → IsZero (L.X i)) :
    stupidTruncMap φ (ComplexShape.embeddingDownNatToIntShift b) ≫
        (restrictExtendDownNatToIntShiftIso L b hL).hom =
      (restrictExtendDownNatToIntShiftIso K b hK).hom ≫ φ := by
  let e := ComplexShape.embeddingDownNatToIntShift b
  let _ : K.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift K b hK
  let _ : L.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift L b hL
  exact restrictExtendIsoOfIsStrictlySupported_hom_naturality e φ

/-- The inverse shifted reconstruction is natural in maps of complexes that
are zero below the same bound. -/
@[reassoc]
theorem restrictExtendDownNatToIntShiftIso_inv_naturality
    {K L : ChainComplex C ℤ} (φ : K ⟶ L) (b : ℤ)
    (hK : ∀ i : ℤ, i < b → IsZero (K.X i))
    (hL : ∀ i : ℤ, i < b → IsZero (L.X i)) :
    φ ≫ (restrictExtendDownNatToIntShiftIso L b hL).inv =
      (restrictExtendDownNatToIntShiftIso K b hK).inv ≫
        stupidTruncMap φ (ComplexShape.embeddingDownNatToIntShift b) := by
  let e := ComplexShape.embeddingDownNatToIntShift b
  let _ : K.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift K b hK
  let _ : L.IsStrictlySupported e :=
    isStrictlySupported_embeddingDownNatToIntShift L b hL
  exact restrictExtendIsoOfIsStrictlySupported_inv_naturality e φ

end Reconstruction

section HomologyFunctor

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [CategoryWithHomology C]

/-- Functor-level cycles comparison for shifted zero extension. -/
noncomputable def cyclesFunctorExtendDownNatToIntShiftIso
    (b : ℤ) (n : ℕ) :
    (ComplexShape.embeddingDownNatToIntShift b).extendFunctor C ⋙
        cyclesFunctor C (ComplexShape.down ℤ) (b + n) ≅
      cyclesFunctor C (ComplexShape.down ℕ) n :=
  extendCyclesFunctorIso
    (ComplexShape.embeddingDownNatToIntShift b) n (b + n) rfl

/-- Functor-level opcycles comparison for shifted zero extension. -/
noncomputable def opcyclesFunctorExtendDownNatToIntShiftIso
    (b : ℤ) (n : ℕ) :
    (ComplexShape.embeddingDownNatToIntShift b).extendFunctor C ⋙
        opcyclesFunctor C (ComplexShape.down ℤ) (b + n) ≅
      opcyclesFunctor C (ComplexShape.down ℕ) n :=
  extendOpcyclesFunctorIso
    (ComplexShape.embeddingDownNatToIntShift b) n (b + n) rfl

/-- Functor-level homology comparison for shifted zero extension. -/
noncomputable def homologyFunctorExtendDownNatToIntShiftIso
    (b : ℤ) (n : ℕ) :
    (ComplexShape.embeddingDownNatToIntShift b).extendFunctor C ⋙
        homologyFunctor C (ComplexShape.down ℤ) (b + n) ≅
      homologyFunctor C (ComplexShape.down ℕ) n :=
  extendHomologyFunctorIso
    (ComplexShape.embeddingDownNatToIntShift b) n (b + n) rfl

end HomologyFunctor

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Cycles of the shifted zero extension in a range degree. -/
noncomputable def cyclesIsoExtendDownNatToIntShift
    (K : ChainComplex C ℕ) (b : ℤ) (n : ℕ) :
    (K.extend (ComplexShape.embeddingDownNatToIntShift b)).cycles (b + n) ≅
      K.cycles n :=
  (cyclesFunctorExtendDownNatToIntShiftIso C b n).app K

/-- Opcycles of the shifted zero extension in a range degree. -/
noncomputable def opcyclesIsoExtendDownNatToIntShift
    (K : ChainComplex C ℕ) (b : ℤ) (n : ℕ) :
    (K.extend (ComplexShape.embeddingDownNatToIntShift b)).opcycles (b + n) ≅
      K.opcycles n :=
  (opcyclesFunctorExtendDownNatToIntShiftIso C b n).app K

/-- Homology of the shifted zero extension in degree `b + n`. -/
noncomputable def homologyIsoExtendDownNatToIntShift
    (K : ChainComplex C ℕ) (b : ℤ) (n : ℕ) :
    (K.extend (ComplexShape.embeddingDownNatToIntShift b)).homology
        (b + n) ≅ K.homology n :=
  (homologyFunctorExtendDownNatToIntShiftIso C b n).app K

/-- Homology of the shifted restriction agrees with homology of the original
integer complex when all terms below the explicit bound are zero. -/
noncomputable def homologyIsoRestrictDownNatToIntShift
    (K : ChainComplex C ℤ) (b : ℤ)
    (hb : ∀ i : ℤ, i < b → IsZero (K.X i)) (n : ℕ) :
    (K.restriction
        (ComplexShape.embeddingDownNatToIntShift b)).homology n ≅
      K.homology (b + n) :=
  (homologyIsoExtendDownNatToIntShift
      (K.restriction (ComplexShape.embeddingDownNatToIntShift b)) b n).symm ≪≫
    HomologicalComplex.homologyMapIso
      (restrictExtendDownNatToIntShiftIso K b hb) (b + n)

/-- Naturality of shifted-extension homology. -/
@[reassoc]
theorem homologyIso_extendDownNatToIntShift_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (b : ℤ) (n : ℕ) :
    homologyMap
        (extendMap φ (ComplexShape.embeddingDownNatToIntShift b)) (b + n) ≫
        (homologyIsoExtendDownNatToIntShift L b n).hom =
      (homologyIsoExtendDownNatToIntShift K b n).hom ≫
        homologyMap φ n :=
  (homologyFunctorExtendDownNatToIntShiftIso C b n).hom.naturality φ

/-- Naturality of the cycles comparison for shifted extension. -/
@[reassoc]
theorem cyclesIso_extendDownNatToIntShift_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (b : ℤ) (n : ℕ) :
    cyclesMap
        (extendMap φ (ComplexShape.embeddingDownNatToIntShift b)) (b + n) ≫
        (cyclesIsoExtendDownNatToIntShift L b n).hom =
      (cyclesIsoExtendDownNatToIntShift K b n).hom ≫ cyclesMap φ n :=
  (cyclesFunctorExtendDownNatToIntShiftIso C b n).hom.naturality φ

/-- Naturality of the opcycles comparison for shifted extension. -/
@[reassoc]
theorem opcyclesIso_extendDownNatToIntShift_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (b : ℤ) (n : ℕ) :
    opcyclesMap
        (extendMap φ (ComplexShape.embeddingDownNatToIntShift b)) (b + n) ≫
        (opcyclesIsoExtendDownNatToIntShift L b n).hom =
      (opcyclesIsoExtendDownNatToIntShift K b n).hom ≫ opcyclesMap φ n :=
  (opcyclesFunctorExtendDownNatToIntShiftIso C b n).hom.naturality φ

/-- Homology of a shifted zero extension vanishes below the lower bound. -/
theorem isZero_homology_extendDownNatToIntShift_lt
    (K : ChainComplex C ℕ) (b z : ℤ) (hz : z < b) :
    IsZero ((K.extend
      (ComplexShape.embeddingDownNatToIntShift b)).homology z) :=
  isZero_homology_extend_of_notMem_range K
    (ComplexShape.embeddingDownNatToIntShift b) z
      ((ComplexShape.notMem_range_embeddingDownNatToIntShift_iff b z).2 hz)

/-- Shifted zero extension preserves and reflects quasi-isomorphisms. -/
theorem quasiIso_extendDownNatToIntShift_iff
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (b : ℤ) :
    QuasiIso (extendMap φ
      (ComplexShape.embeddingDownNatToIntShift b)) ↔ QuasiIso φ :=
  quasiIso_extendMap_iff φ (ComplexShape.embeddingDownNatToIntShift b)

end Homology

end HomologicalComplex

namespace ShortComplex.ShortExact

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Shifted zero extension preserves short exact sequences. -/
theorem map_embeddingDownNatToIntShiftExtend
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact) (b : ℤ) :
    (S.map ((ComplexShape.embeddingDownNatToIntShift b).extendFunctor C)).ShortExact :=
  map_extendFunctor (ComplexShape.embeddingDownNatToIntShift b) S hS

/-- Shifted zero extension reflects as well as preserves short exactness. -/
theorem map_embeddingDownNatToIntShiftExtend_iff
    (S : ShortComplex (ChainComplex C ℕ)) (b : ℤ) :
    (S.map ((ComplexShape.embeddingDownNatToIntShift b).extendFunctor C)).ShortExact ↔
      S.ShortExact := by
  constructor
  · intro hS
    rw [HomologicalComplex.shortExact_iff_degreewise_shortExact] at hS ⊢
    intro n
    let e := ComplexShape.embeddingDownNatToIntShift b
    let F := e.extendFunctor C
    let T : ShortComplex C :=
      (S.map F).map (HomologicalComplex.eval C (ComplexShape.down ℤ) (e.f n))
    let U : ShortComplex C :=
      S.map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    let e₁ : T.X₁ ≅ U.X₁ := S.X₁.extendXIso e rfl
    let e₂ : T.X₂ ≅ U.X₂ := S.X₂.extendXIso e rfl
    let e₃ : T.X₃ ≅ U.X₃ := S.X₃.extendXIso e rfl
    have h₁₂ : e₁.hom ≫ U.f = T.f ≫ e₂.hom := by
      change (S.X₁.extendXIso e rfl).hom ≫ S.f.f n =
        (HomologicalComplex.extendMap S.f e).f (e.f n) ≫
          (S.X₂.extendXIso e rfl).hom
      rw [HomologicalComplex.extendMap_f S.f e rfl]
      simp
    have h₂₃ : e₂.hom ≫ U.g = T.g ≫ e₃.hom := by
      change (S.X₂.extendXIso e rfl).hom ≫ S.g.f n =
        (HomologicalComplex.extendMap S.g e).f (e.f n) ≫
          (S.X₃.extendXIso e rfl).hom
      rw [HomologicalComplex.extendMap_f S.g e rfl]
      simp
    let iso : T ≅ U := ShortComplex.isoMk e₁ e₂ e₃ h₁₂ h₂₃
    exact ShortComplex.shortExact_of_iso iso (hS (e.f n))
  · exact fun hS => map_embeddingDownNatToIntShiftExtend S hS b

/-- The connecting morphism of an extended short exact sequence agrees with
the original connecting morphism in shifted range degrees. -/
theorem delta_extendDownNatToIntShift
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact)
    (b : ℤ) (n : ℕ)
    (hijNat : (ComplexShape.down ℕ).Rel (n + 1) n)
    (hijInt : (ComplexShape.down ℤ).Rel
      (b + ((n + 1 : ℕ) : ℤ)) (b + n)) :
    (S.X₃.extendHomologyIso
        (ComplexShape.embeddingDownNatToIntShift b) rfl).hom ≫
        hS.δ (n + 1) n hijNat =
      (map_extendFunctor (ComplexShape.embeddingDownNatToIntShift b) S hS).δ
          (b + ((n + 1 : ℕ) : ℤ)) (b + n) hijInt ≫
        (S.X₁.extendHomologyIso
          (ComplexShape.embeddingDownNatToIntShift b) rfl).hom :=
  map_extendFunctor_δ (ComplexShape.embeddingDownNatToIntShift b) S hS
    (n + 1) n (b + ((n + 1 : ℕ) : ℤ)) (b + n)
      rfl rfl hijNat hijInt

end

end ShortComplex.ShortExact

namespace Homotopy

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable {K L : ChainComplex C ℕ} {f g : K ⟶ L}

/-- Extension along the shifted embedding preserves and reflects chain
homotopies. -/
noncomputable def extendDownNatToIntShiftEquiv (b : ℤ) :
    Homotopy f g ≃
      Homotopy
        (HomologicalComplex.extendMap f
          (ComplexShape.embeddingDownNatToIntShift b))
        (HomologicalComplex.extendMap g
          (ComplexShape.embeddingDownNatToIntShift b)) :=
  Homotopy.extendEquiv (ComplexShape.embeddingDownNatToIntShift b)

end

end Homotopy

/-- Shifted zero extension preserves and reflects homotopy equivalences. -/
theorem HomologicalComplex.homotopyEquivalences_extendDownNatToIntShift_iff
    {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (b : ℤ) :
    homotopyEquivalences C (ComplexShape.down ℤ)
        (HomologicalComplex.extendMap f
          (ComplexShape.embeddingDownNatToIntShift b)) ↔
      homotopyEquivalences C (ComplexShape.down ℕ) f :=
  HomologicalComplex.homotopyEquivalences_extendMap_iff f
    (ComplexShape.embeddingDownNatToIntShift b)

end
