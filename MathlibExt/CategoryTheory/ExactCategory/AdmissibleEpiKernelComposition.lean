/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty

/-!
# Kernels of composites of admissible epimorphisms

For an admissible epimorphism in an exact category, this file packages an
explicit admissible exact kernel presentation.  It then base-changes such a
presentation along an arbitrary morphism and constructs the kernel
presentation of a composite of two admissible epimorphisms.

For `A --p--> B --q--> D`, Lean's diagrammatic composite is `p ≫ q`.  The
pullback of `p` along the kernel inclusion of `q` is the kernel object of this
composite, and its pulled-back kernel row is the admissible exact sequence

```text
ker(p) --> ker(p ≫ q) --> ker(q).
```

The construction uses closure of admissible epimorphisms under composition
and isomorphism, the exact-category pullback axiom for admissible epimorphisms,
and kernel and cokernel universal properties. It requires neither a balanced
nor an abelian category and introduces no global pullback, exactness, or limit
instance.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Preadditive ZeroObject

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- An explicit admissible exact kernel presentation of an admissible
epimorphism `p : A ⟶ B`. -/
structure AdmissibleEpiKernelPresentation {A B : C} (p : A ⟶ B) where
  kernel : C
  ι : kernel ⟶ A
  zero : ι ≫ p = 0
  exact : IsAdmissibleExact (ShortComplex.mk ι p zero)

namespace AdmissibleEpiKernelPresentation

variable {A B : C} {p : A ⟶ B}

/-- Every admissible epimorphism admits an explicit kernel presentation. -/
theorem nonempty (hp : IsAdmissibleEpi p) :
    Nonempty (AdmissibleEpiKernelPresentation p) := by
  rcases hp with ⟨K, i, w, h⟩
  exact ⟨{ kernel := K, ι := i, zero := w, exact := h }⟩

/-- The stored first map is an admissible monomorphism. -/
theorem ι_admissible (P : AdmissibleEpiKernelPresentation p) :
    IsAdmissibleMono P.ι :=
  isAdmissibleMono_f P.exact

/-- The presented morphism is an admissible epimorphism. -/
theorem epi_admissible (P : AdmissibleEpiKernelPresentation p) :
    IsAdmissibleEpi p :=
  isAdmissibleEpi_g P.exact

/-- The stored inclusion has the kernel universal property. -/
noncomputable def kernelIsLimit (P : AdmissibleEpiKernelPresentation p) :
    IsLimit (KernelFork.ofι P.ι P.zero) :=
  isLimit_kernelFork_of_isAdmissibleExact P.exact

/-- The presented epimorphism has the cokernel universal property. -/
noncomputable def cokernelIsColimit (P : AdmissibleEpiKernelPresentation p) :
    IsColimit (CokernelCofork.ofπ p P.zero) :=
  isColimit_cokernelCofork_of_isAdmissibleExact P.exact

/-- Pullback data for an explicit admissible-epi kernel presentation. -/
structure BaseChange (P : AdmissibleEpiKernelPresentation p)
    {Z : C} (g : Z ⟶ B) where
  obj : C
  fst : obj ⟶ Z
  snd : obj ⟶ A
  square : IsPullback fst snd g p
  fst_admissible : IsAdmissibleEpi fst

/-- Exact-category pullback data exists for a presented admissible epi along
an arbitrary morphism. -/
theorem baseChange_nonempty (P : AdmissibleEpiKernelPresentation p)
    {Z : C} (g : Z ⟶ B) : Nonempty (P.BaseChange g) := by
  obtain ⟨P', fst, snd, hpb, hfst⟩ :=
    admissibleEpi_pullback A B p P.epi_admissible Z g
  exact ⟨
    { obj := P'
      fst := fst
      snd := snd
      square := hpb
      fst_admissible := hfst }⟩

/-- Choose the exact-category pullback of the presented admissible epi along
an arbitrary morphism. -/
noncomputable def baseChange (P : AdmissibleEpiKernelPresentation p)
    {Z : C} (g : Z ⟶ B) : P.BaseChange g :=
  (P.baseChange_nonempty g).some

namespace BaseChange

variable (P : AdmissibleEpiKernelPresentation p)
variable {Z : C} {g : Z ⟶ B} (Q : P.BaseChange g)

/-- The original kernel inclusion lifted to the pullback object. -/
noncomputable def kernelLift : P.kernel ⟶ Q.obj :=
  Q.square.lift (0 : P.kernel ⟶ Z) P.ι (by simp [P.zero])

@[reassoc (attr := simp)]
theorem kernelLift_fst : Q.kernelLift ≫ Q.fst = 0 := by
  exact Q.square.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem kernelLift_snd : Q.kernelLift ≫ Q.snd = P.ι := by
  exact Q.square.lift_snd _ _ _

/-- The lifted original kernel is a kernel of the pulled-back admissible
epimorphism. -/
noncomputable def kernelLiftIsLimit :
    IsLimit (KernelFork.ofι Q.kernelLift Q.kernelLift_fst) := by
  let hK := P.kernelIsLimit
  let _ : Mono P.ι := IsAdmissibleMono.mono P.ι_admissible
  refine KernelFork.IsLimit.ofι Q.kernelLift Q.kernelLift_fst
    (fun {W} h hh => ?_) (fun {W} h hh => ?_) (fun {W} h hh m hm => ?_)
  · have hsnd : (h ≫ Q.snd) ≫ p = 0 := by
      calc
        (h ≫ Q.snd) ≫ p = h ≫ (Q.snd ≫ p) := Category.assoc _ _ _
        _ = h ≫ (Q.fst ≫ g) := by rw [Q.square.w]
        _ = (h ≫ Q.fst) ≫ g := (Category.assoc _ _ _).symm
        _ = 0 := by rw [hh, zero_comp]
    exact hK.lift (KernelFork.ofι (h ≫ Q.snd) hsnd)
  · have hsnd : (h ≫ Q.snd) ≫ p = 0 := by
      calc
        (h ≫ Q.snd) ≫ p = h ≫ (Q.snd ≫ p) := Category.assoc _ _ _
        _ = h ≫ (Q.fst ≫ g) := by rw [Q.square.w]
        _ = (h ≫ Q.fst) ≫ g := (Category.assoc _ _ _).symm
        _ = 0 := by rw [hh, zero_comp]
    apply Q.square.hom_ext
    · rw [Category.assoc, Q.kernelLift_fst, comp_zero, hh]
    · rw [Category.assoc, Q.kernelLift_snd]
      exact hK.fac (KernelFork.ofι (h ≫ Q.snd) hsnd) WalkingParallelPair.zero
  · apply (cancel_mono P.ι).mp
    calc
      (m ≫ P.ι) = (m ≫ Q.kernelLift) ≫ Q.snd := by
        rw [Category.assoc, Q.kernelLift_snd]
      _ = h ≫ Q.snd := by rw [hm]
      _ = (hK.lift (KernelFork.ofι (h ≫ Q.snd) (by
          calc
            (h ≫ Q.snd) ≫ p = h ≫ (Q.snd ≫ p) := Category.assoc _ _ _
            _ = h ≫ (Q.fst ≫ g) := by rw [Q.square.w]
            _ = (h ≫ Q.fst) ≫ g := (Category.assoc _ _ _).symm
            _ = 0 := by rw [hh, zero_comp]))) ≫ P.ι := by
        symm
        exact hK.fac _ WalkingParallelPair.zero

/-- The pulled-back admissible epi, with the original kernel object and its
lift, is again an explicit admissible exact kernel presentation. -/
noncomputable def kernelPresentation :
    AdmissibleEpiKernelPresentation Q.fst := by
  let J := (AdmissibleEpiKernelPresentation.nonempty Q.fst_admissible).some
  let hLift := Q.kernelLiftIsLimit
  let hJLim := J.kernelIsLimit
  let e : P.kernel ≅ J.kernel := hLift.conePointUniqueUpToIso hJLim
  have he : e.hom ≫ J.ι = Q.kernelLift := by
    have h := IsLimit.conePointUniqueUpToIso_hom_comp
      hLift hJLim WalkingParallelPair.zero
    simpa [KernelFork.ofι] using h
  let S₁ : ShortComplex C :=
    ShortComplex.mk Q.kernelLift Q.fst Q.kernelLift_fst
  let S₂ : ShortComplex C := ShortComplex.mk J.ι Q.fst J.zero
  have hIso : S₂ ≅ S₁ :=
    ShortComplex.isoMk e.symm (Iso.refl Q.obj) (Iso.refl Z)
      (by
        dsimp [S₁, S₂]
        rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp,
          Category.comp_id])
      (by simp [S₁, S₂])
  exact
    { kernel := P.kernel
      ι := Q.kernelLift
      zero := Q.kernelLift_fst
      exact := isAdmissibleExact_of_iso hIso J.exact }

@[simp]
theorem kernelPresentation_kernel : Q.kernelPresentation.kernel = P.kernel := by
  rfl

@[simp]
theorem kernelPresentation_ι : Q.kernelPresentation.ι = Q.kernelLift := by
  rfl

end BaseChange

section Composite

variable {D : C} {q : B ⟶ D}

/-- The pullback object used as the kernel of `p ≫ q`: pull `p` back along
the chosen kernel inclusion of `q`. -/
noncomputable def compositeBaseChange
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) : P.BaseChange Q.ι :=
  P.baseChange Q.ι

/-- Explicit kernel presentation of the diagrammatic composite `p ≫ q`. -/
noncomputable def composite
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    AdmissibleEpiKernelPresentation (p ≫ q) := by
  let R := compositeBaseChange P Q
  let hMono : IsAdmissibleMono R.snd :=
    isAdmissibleMono_of_isPullback R.square Q.ι_admissible P.epi_admissible
  have w : R.snd ≫ (p ≫ q) = 0 := by
    calc
      R.snd ≫ (p ≫ q) = (R.snd ≫ p) ≫ q := (Category.assoc _ _ _).symm
      _ = (R.fst ≫ Q.ι) ≫ q := by rw [R.square.w]
      _ = R.fst ≫ (Q.ι ≫ q) := Category.assoc _ _ _
      _ = 0 := by rw [Q.zero, comp_zero]
  let hP := P.cokernelIsColimit
  let hQ := Q.cokernelIsColimit
  let descB {W : C} (f : A ⟶ W) (hf : R.snd ≫ f = 0) : B ⟶ W :=
    hP.desc (CokernelCofork.ofπ f (by
      calc
        P.ι ≫ f = (R.kernelLift ≫ R.snd) ≫ f := by
          rw [R.kernelLift_snd]
        _ = R.kernelLift ≫ (R.snd ≫ f) := Category.assoc _ _ _
        _ = 0 := by rw [hf, comp_zero]))
  have descB_fac {W : C} (f : A ⟶ W) (hf : R.snd ≫ f = 0) :
      p ≫ descB f hf = f := by
    exact Cofork.IsColimit.π_desc hP
  have kernelQ_descB {W : C} (f : A ⟶ W) (hf : R.snd ≫ f = 0) :
      Q.ι ≫ descB f hf = 0 := by
    let _ : Epi R.fst := IsAdmissibleEpi.epi R.fst_admissible
    apply (cancel_epi R.fst).mp
    have hzero : R.fst ≫ (Q.ι ≫ descB f hf) = 0 := by
      calc
      R.fst ≫ (Q.ι ≫ descB f hf) =
          (R.fst ≫ Q.ι) ≫ descB f hf := (Category.assoc _ _ _).symm
      _ = (R.snd ≫ p) ≫ descB f hf := by rw [R.square.w]
      _ = R.snd ≫ (p ≫ descB f hf) := Category.assoc _ _ _
      _ = R.snd ≫ f := by rw [descB_fac f hf]
      _ = 0 := hf
    simpa only [comp_zero] using hzero
  let descD {W : C} (f : A ⟶ W) (hf : R.snd ≫ f = 0) : D ⟶ W :=
    hQ.desc (CokernelCofork.ofπ (descB f hf) (kernelQ_descB f hf))
  have descD_fac {W : C} (f : A ⟶ W) (hf : R.snd ≫ f = 0) :
      (p ≫ q) ≫ descD f hf = f := by
    have hq : q ≫ descD f hf = descB f hf := by
      change q ≫ hQ.desc (CokernelCofork.ofπ (descB f hf) _) = _
      exact Cofork.IsColimit.π_desc hQ
    calc
      (p ≫ q) ≫ descD f hf = p ≫ (q ≫ descD f hf) := Category.assoc _ _ _
      _ = p ≫ descB f hf := by rw [hq]
      _ = f := descB_fac f hf
  let hCok : IsColimit (CokernelCofork.ofπ (p ≫ q) w) :=
    CokernelCofork.IsColimit.ofπ (p ≫ q) w
      (fun f hf => descD f hf) (fun f hf => descD_fac f hf) (by
        intro W f hf d hd
        let _ : Epi p := IsAdmissibleEpi.epi P.epi_admissible
        apply Cofork.IsColimit.hom_ext hQ
        change q ≫ d = q ≫ descD f hf
        have hq : q ≫ descD f hf = descB f hf := by
          change q ≫ hQ.desc (CokernelCofork.ofπ (descB f hf) _) = _
          exact Cofork.IsColimit.π_desc hQ
        rw [hq]
        apply (cancel_epi p).mp
        calc
          p ≫ (q ≫ d) = (p ≫ q) ≫ d := (Category.assoc _ _ _).symm
          _ = f := hd
          _ = p ≫ descB f hf := (descB_fac f hf).symm)
  exact
    { kernel := R.obj
      ι := R.snd
      zero := w
      exact := isAdmissibleExact_of_isAdmissibleMono_isColimit hMono hCok }

@[simp]
theorem composite_kernel
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (P.composite Q).kernel = (compositeBaseChange P Q).obj := by
  rfl

@[simp]
theorem composite_ι
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (P.composite Q).ι = (compositeBaseChange P Q).snd := by
  rfl

/-- The canonical kernel row associated to two explicit presentations of
composable admissible epimorphisms. -/
noncomputable def compositeKernelSequence
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) : ShortComplex C :=
  let R := compositeBaseChange P Q
  let K := R.kernelPresentation
  ShortComplex.mk K.ι R.fst K.zero

/-- The kernel row `ker(p) ⟶ ker(p ≫ q) ⟶ ker(q)` is admissible exact. -/
theorem compositeKernelSequence_exact
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    IsAdmissibleExact (compositeKernelSequence P Q) := by
  let R := compositeBaseChange P Q
  change IsAdmissibleExact
    (ShortComplex.mk R.kernelPresentation.ι R.fst R.kernelPresentation.zero)
  exact R.kernelPresentation.exact

@[simp]
theorem compositeKernelSequence_X₁
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).X₁ = P.kernel := by
  simp [compositeKernelSequence]

@[simp]
theorem compositeKernelSequence_X₂
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).X₂ = (compositeBaseChange P Q).obj :=
  rfl

/-- The middle object of the kernel row is the chosen kernel object of the
composite presentation. -/
theorem compositeKernelSequence_X₂_eq_composite_kernel
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).X₂ = (P.composite Q).kernel := by
  rw [compositeKernelSequence_X₂, composite_kernel]

@[simp]
theorem compositeKernelSequence_X₃
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).X₃ = Q.kernel :=
  rfl

@[simp]
theorem compositeKernelSequence_f
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).f =
      (compositeBaseChange P Q).kernelLift := by
  simp [compositeKernelSequence]
  rfl

@[simp]
theorem compositeKernelSequence_g
    (P : AdmissibleEpiKernelPresentation p)
    (Q : AdmissibleEpiKernelPresentation q) :
    (compositeKernelSequence P Q).g = (compositeBaseChange P Q).fst :=
  rfl

end Composite

end AdmissibleEpiKernelPresentation

end CategoryTheory.ExactCategory

end
