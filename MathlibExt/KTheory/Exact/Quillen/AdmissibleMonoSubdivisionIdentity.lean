/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoSubdivisionSpan

/-!
# Identity coherence for the admissible-mono subdivision Q-map

For an admissible mono `i : A ↪ B`, the identity subdivision square gives
the flag `0 → A → A → B → B`.  The two raw interval-span legs are
isomorphisms: the discarded left and right quotient intervals are quotients
of identities and hence zero.  After the canonical quotient transports, the
two legs agree by cancellation against the apex quotient projection.  This
identifies the resulting raw span with the identity span and proves the
quotient-level Quillen morphism preserves identities.

No composition or bundled-functor claim is made here.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- In the identity triple flag, the left interval-span leg is an
isomorphism. -/
theorem admissibleMonoIdentityTripleIntervalSpan_l_isIso
    {A B : C} (i : A ⟶ B) (hi : IsAdmissibleMono i) :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
      (𝟙 A) (IsAdmissibleMono.id A) i hi
      (𝟙 B) (IsAdmissibleMono.id B)).l) := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    (𝟙 A) (IsAdmissibleMono.id A) i hi
    (𝟙 B) (IsAdmissibleMono.id B)
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  have hmap : F.chain.map (homOfLE h12) = 𝟙 A := by
    rfl
  let _ : IsIso (F.chain.map (homOfLE h12)) :=
    hmap.symm ▸ IsIso.id A
  have hz : IsZero (F.intervalQuotient (1 : Fin 5) (2 : Fin 5) h12) :=
    F.intervalQuotient_isZero_of_isIso h12
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  have hIso : IsIso
      (F.intervalMap (h12.trans h23) h23 h12 le_rfl) :=
    isIso_g_of_isAdmissibleExact_of_isZero
      (F.interval_triple_exact h12 h23) hz
  simpa only [AdmissibleMonoFlag.intervalQuillenSpan_l] using hIso

/-- In the identity triple flag, the right interval-span leg is an
isomorphism. -/
theorem admissibleMonoIdentityTripleIntervalSpan_r_isIso
    {A B : C} (i : A ⟶ B) (hi : IsAdmissibleMono i) :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
      (𝟙 A) (IsAdmissibleMono.id A) i hi
      (𝟙 B) (IsAdmissibleMono.id B)).r) := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    (𝟙 A) (IsAdmissibleMono.id A) i hi
    (𝟙 B) (IsAdmissibleMono.id B)
  let h13 : (1 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  have hmap : F.chain.map (homOfLE h34) = 𝟙 B := by
    rfl
  let _ : IsIso (F.chain.map (homOfLE h34)) :=
    hmap.symm ▸ IsIso.id B
  have hz : IsZero (F.intervalQuotient (3 : Fin 5) (4 : Fin 5) h34) :=
    F.intervalQuotient_isZero_of_isIso h34
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  have hIso : IsIso
      (F.intervalMap h13 (h13.trans h34) le_rfl h34) :=
    isIso_f_of_isAdmissibleExact_of_isZero
      (F.interval_triple_exact h13 h34) hz
  simpa only [AdmissibleMonoFlag.intervalQuillenSpan_r] using hIso

/-- If the first mono of a triple is an isomorphism, the left interval-span
leg is an isomorphism. -/
theorem admissibleMonoTripleIntervalSpan_l_isIso_of_left_isIso
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f) [IsIso f]
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
      f hf g hg h hh).l) := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag f hf g hg h hh
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  have hmap : F.chain.map (homOfLE h12) = f := by rfl
  let _ : IsIso (F.chain.map (homOfLE h12)) :=
    hmap.symm ▸ (inferInstance : IsIso f)
  have hz : IsZero (F.intervalQuotient (1 : Fin 5) (2 : Fin 5) h12) :=
    F.intervalQuotient_isZero_of_isIso h12
  have hIso : IsIso
      (F.intervalMap (h12.trans h23) h23 h12 le_rfl) :=
    isIso_g_of_isAdmissibleExact_of_isZero
      (F.interval_triple_exact h12 h23) hz
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  simpa only [AdmissibleMonoFlag.intervalQuillenSpan_l] using hIso

/-- If the last mono of a triple is an isomorphism, the right interval-span
leg is an isomorphism. -/
theorem admissibleMonoTripleIntervalSpan_r_isIso_of_right_isIso
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) [IsIso h] :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
      f hf g hg h hh).r) := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag f hf g hg h hh
  let h13 : (1 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  have hmap : F.chain.map (homOfLE h34) = h := by rfl
  let _ : IsIso (F.chain.map (homOfLE h34)) :=
    hmap.symm ▸ (inferInstance : IsIso h)
  have hz : IsZero (F.intervalQuotient (3 : Fin 5) (4 : Fin 5) h34) :=
    F.intervalQuotient_isZero_of_isIso h34
  have hIso : IsIso
      (F.intervalMap h13 (h13.trans h34) le_rfl h34) :=
    isIso_f_of_isAdmissibleExact_of_isZero
      (F.interval_triple_exact h13 h34) hz
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  simpa only [AdmissibleMonoFlag.intervalQuillenSpan_r] using hIso

/-- Endpoint transport preserves invertibility of the left leg of the
identity triple span. -/
theorem admissibleMonoIdentityTripleQuillenSpan_l_isIso
    {A B : C} (i : A ⟶ B) (hi : IsAdmissibleMono i) :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
      (𝟙 A) (IsAdmissibleMono.id A) i hi
      (𝟙 B) (IsAdmissibleMono.id B)).l) := by
  have hRaw := admissibleMonoIdentityTripleIntervalSpan_l_isIso i hi
  let _ := hRaw
  change IsIso
    ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
        (𝟙 A) (IsAdmissibleMono.id A) i hi
        (𝟙 B) (IsAdmissibleMono.id B)).l ≫
      (AdmissibleMonoFlag.admissibleMonoTripleSourceIso
        (𝟙 A) (IsAdmissibleMono.id A) i hi
        (𝟙 B) (IsAdmissibleMono.id B)).hom)
  infer_instance

/-- Endpoint transport preserves invertibility of the right leg of the
identity triple span. -/
theorem admissibleMonoIdentityTripleQuillenSpan_r_isIso
    {A B : C} (i : A ⟶ B) (hi : IsAdmissibleMono i) :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
      (𝟙 A) (IsAdmissibleMono.id A) i hi
      (𝟙 B) (IsAdmissibleMono.id B)).r) := by
  have hRaw := admissibleMonoIdentityTripleIntervalSpan_r_isIso i hi
  let _ := hRaw
  change IsIso
    ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
        (𝟙 A) (IsAdmissibleMono.id A) i hi
        (𝟙 B) (IsAdmissibleMono.id B)).r ≫
      (AdmissibleMonoFlag.admissibleMonoTripleTargetIso
        (𝟙 A) (IsAdmissibleMono.id A) i hi
        (𝟙 B) (IsAdmissibleMono.id B)).hom)
  infer_instance

/-- Endpoint transport preserves the left-leg isomorphism supplied by an
invertible first mono. -/
theorem admissibleMonoTripleQuillenSpan_l_isIso_of_left_isIso
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f) [IsIso f]
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
      f hf g hg h hh).l) := by
  have hRaw := admissibleMonoTripleIntervalSpan_l_isIso_of_left_isIso
    f hf g hg h hh
  let _ := hRaw
  change IsIso
    ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
        f hf g hg h hh).l ≫
      (AdmissibleMonoFlag.admissibleMonoTripleSourceIso
        f hf g hg h hh).hom)
  infer_instance

/-- Endpoint transport preserves the right-leg isomorphism supplied by an
invertible last mono. -/
theorem admissibleMonoTripleQuillenSpan_r_isIso_of_right_isIso
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) [IsIso h] :
    IsIso ((AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
      f hf g hg h hh).r) := by
  have hRaw := admissibleMonoTripleIntervalSpan_r_isIso_of_right_isIso
    f hf g hg h hh
  let _ := hRaw
  change IsIso
    ((AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
        f hf g hg h hh).r ≫
      (AdmissibleMonoFlag.admissibleMonoTripleTargetIso
        f hf g hg h hh).hom)
  infer_instance

/-- A subdivision span has invertible left leg when its backwards source
leg is invertible. -/
theorem admissibleMonoSubdivisionQuillenSpan_l_isIso_of_left_isIso
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y)
    [IsIso w.hom.1.unop.hom] :
    IsIso ((admissibleMonoSubdivisionQuillenSpan w).l) := by
  have hTriple := admissibleMonoTripleQuillenSpan_l_isIso_of_left_isIso
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let _ := hTriple
  unfold admissibleMonoSubdivisionQuillenSpan
  dsimp only
  change IsIso (_ ≫ (Iso.refl _).hom)
  infer_instance

/-- A subdivision span has invertible right leg when its forwards target
leg is invertible. -/
theorem admissibleMonoSubdivisionQuillenSpan_r_isIso_of_right_isIso
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y)
    [IsIso w.hom.2.hom] :
    IsIso ((admissibleMonoSubdivisionQuillenSpan w).r) := by
  have hTriple := admissibleMonoTripleQuillenSpan_r_isIso_of_right_isIso
    w.hom.1.unop.hom w.hom.1.unop.property
    x.val.hom x.val.property w.hom.2.hom w.hom.2.property
  let _ := hTriple
  unfold admissibleMonoSubdivisionQuillenSpan
  dsimp only
  change IsIso (_ ≫ _)
  infer_instance

/-- The left leg of the subdivision span of an identity is invertible. -/
theorem admissibleMonoSubdivisionQuillenSpan_id_l_isIso
    (x : AdmissibleMonoSubdivision (C := C)) :
    IsIso ((admissibleMonoSubdivisionQuillenSpan (𝟙 x)).l) := by
  let _ : IsIso
      ((Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom) := by
    change IsIso (𝟙 _)
    exact IsIso.id _
  exact admissibleMonoSubdivisionQuillenSpan_l_isIso_of_left_isIso (𝟙 x)

/-- The right leg of the subdivision span of an identity is invertible. -/
theorem admissibleMonoSubdivisionQuillenSpan_id_r_isIso
    (x : AdmissibleMonoSubdivision (C := C)) :
    IsIso ((admissibleMonoSubdivisionQuillenSpan (𝟙 x)).r) := by
  let _ : IsIso
      ((Functor.Elements.Hom.hom (𝟙 x)).2.hom) := by
    change IsIso (𝟙 _)
    exact IsIso.id _
  exact admissibleMonoSubdivisionQuillenSpan_r_isIso_of_right_isIso (𝟙 x)

/-- Quotient projection from the target of an admissible mono to the apex of
its identity subdivision span.  The equality cast deliberately uses the
literal apex formula for the underlying interval span, so the public type
does not expose the implementation data selecting interval quotients. -/
noncomputable def admissibleMonoSubdivisionQuillenSpan_id_apexπ
    (x : AdmissibleMonoSubdivision (C := C)) :
    x.obj.2.obj ⟶ (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).apex := by
  let w : x ⟶ x := 𝟙 x
  let a := w.hom.1.unop
  let b := w.hom.2
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    a.hom a.property x.val.hom x.val.property b.hom b.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  let eApex := F.intervalQuillenSpan_apex h12 h23 h34
  change x.obj.2.obj ⟶ (F.intervalQuillenSpan h12 h23 h34).apex
  exact F.intervalπ (1 : Fin 5) (3 : Fin 5) h13 ≫ eqToHom eApex.symm

/-- The apex projection followed by the left leg of the identity
subdivision span is the selected quotient projection. -/
@[reassoc]
theorem admissibleMonoSubdivisionQuillenSpan_id_apexπ_l
    (x : AdmissibleMonoSubdivision (C := C)) :
    admissibleMonoSubdivisionQuillenSpan_id_apexπ x ≫
        (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).l =
      AdmissibleMonoFlag.admissibleMonoQuotientπ
        x.val.hom x.val.property := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    (Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom
    (Functor.Elements.Hom.hom (𝟙 x)).1.unop.property
    x.val.hom x.val.property
    (Functor.Elements.Hom.hom (𝟙 x)).2.hom
    (Functor.Elements.Hom.hom (𝟙 x)).2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  have hmap : F.chain.map (homOfLE (le_rfl : (3 : Fin 5) ≤ 3)) =
      𝟙 (F.chain.obj (3 : Fin 5)) := by
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
  have hSource :=
    AdmissibleMonoFlag.admissibleMonoTripleSourceIso_projection
      (Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom
      (Functor.Elements.Hom.hom (𝟙 x)).1.unop.property
      x.val.hom x.val.property
      (Functor.Elements.Hom.hom (𝟙 x)).2.hom
      (Functor.Elements.Hom.hom (𝟙 x)).2.property
  unfold admissibleMonoSubdivisionQuillenSpan_id_apexπ
  unfold admissibleMonoSubdivisionQuillenSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_apex, eqToHom_refl,
    id_eq, QuillenSpan.endpointTransport_l, Iso.refl_hom,
    Category.comp_id]
  unfold AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
  simp only [QuillenSpan.endpointTransport_l]
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_l]
  rw [F.intervalπ_naturality_assoc h13 h23 h12 le_rfl, hmap,
    Category.id_comp]
  simpa only using hSource

/-- The apex projection followed by the right leg of the identity
subdivision span is the selected quotient projection. -/
@[reassoc]
theorem admissibleMonoSubdivisionQuillenSpan_id_apexπ_r
    (x : AdmissibleMonoSubdivision (C := C)) :
    admissibleMonoSubdivisionQuillenSpan_id_apexπ x ≫
        (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).r =
      AdmissibleMonoFlag.admissibleMonoQuotientπ
        x.val.hom x.val.property := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    (Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom
    (Functor.Elements.Hom.hom (𝟙 x)).1.unop.property
    x.val.hom x.val.property
    (Functor.Elements.Hom.hom (𝟙 x)).2.hom
    (Functor.Elements.Hom.hom (𝟙 x)).2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  let h14 := h13.trans h34
  have hmap : F.chain.map (homOfLE h34) =
      𝟙 (F.chain.obj (3 : Fin 5)) := by
    rfl
  have hTarget :=
    AdmissibleMonoFlag.admissibleMonoTripleTargetIso_projection
      (Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom
      (Functor.Elements.Hom.hom (𝟙 x)).1.unop.property
      x.val.hom x.val.property
      (Functor.Elements.Hom.hom (𝟙 x)).2.hom
      (Functor.Elements.Hom.hom (𝟙 x)).2.property
  let hcomp :=
    AdmissibleMonoFlag.admissibleMonoTriple_comp_admissible
      (Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom
      (Functor.Elements.Hom.hom (𝟙 x)).1.unop.property
      x.val.hom x.val.property
      (Functor.Elements.Hom.hom (𝟙 x)).2.hom
      (Functor.Elements.Hom.hom (𝟙 x)).2.property
  have hEqualQuotient :=
    AdmissibleMonoFlag.admissibleMonoQuotientπ_isoOfEq_hom
      hcomp x.val.property
        (admissibleMonoSubdivisionHom_factorization (𝟙 x))
  unfold admissibleMonoSubdivisionQuillenSpan_id_apexπ
  unfold admissibleMonoSubdivisionQuillenSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_apex, eqToHom_refl,
    id_eq, QuillenSpan.endpointTransport_r, Category.comp_id]
  unfold AdmissibleMonoFlag.admissibleMonoTripleQuillenSpan
  simp only [QuillenSpan.endpointTransport_r, Category.assoc]
  unfold AdmissibleMonoFlag.admissibleMonoTripleIntervalSpan
  dsimp only
  simp only [AdmissibleMonoFlag.intervalQuillenSpan_r]
  rw [F.intervalπ_naturality_assoc h13 h14 le_rfl h34, hmap,
    Category.id_comp]
  rw [← Category.assoc, hTarget]
  rw [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  simpa only [eqToIso_refl, Iso.refl_hom, Category.id_comp,
    Category.assoc] using hEqualQuotient

/-- The canonical projection onto the apex of an identity subdivision span
is an admissible epimorphism. -/
theorem admissibleMonoSubdivisionQuillenSpan_id_apexπ_isAdmissibleEpi
    (x : AdmissibleMonoSubdivision (C := C)) :
    IsAdmissibleEpi (admissibleMonoSubdivisionQuillenSpan_id_apexπ x) := by
  let F := AdmissibleMonoFlag.admissibleMonoTripleFlag
    (Functor.Elements.Hom.hom (𝟙 x)).1.unop.hom
    (Functor.Elements.Hom.hom (𝟙 x)).1.unop.property
    x.val.hom x.val.property
    (Functor.Elements.Hom.hom (𝟙 x)).2.hom
    (Functor.Elements.Hom.hom (𝟙 x)).2.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  let eApex := F.intervalQuillenSpan_apex h12 h23 h34
  have hπ : IsAdmissibleEpi
      (F.intervalπ (1 : Fin 5) (3 : Fin 5) h13) :=
    isAdmissibleEpi_g (F.interval_exact (1 : Fin 5) (3 : Fin 5) h13)
  have hCast : IsAdmissibleEpi (eqToHom eApex.symm) :=
    IsAdmissibleEpi.of_isIso _
  unfold admissibleMonoSubdivisionQuillenSpan_id_apexπ
  exact admissibleEpi_comp.comp_mem _ _ hπ hCast

/-- The two legs of an identity subdivision span agree. -/
theorem admissibleMonoSubdivisionQuillenSpan_id_l_eq_r
    (x : AdmissibleMonoSubdivision (C := C)) :
    (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).l =
      (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).r := by
  let _ : Epi (admissibleMonoSubdivisionQuillenSpan_id_apexπ x) :=
    (admissibleMonoSubdivisionQuillenSpan_id_apexπ_isAdmissibleEpi x).epi
  apply (cancel_epi
    (admissibleMonoSubdivisionQuillenSpan_id_apexπ x)).1
  rw [admissibleMonoSubdivisionQuillenSpan_id_apexπ_l,
    admissibleMonoSubdivisionQuillenSpan_id_apexπ_r]

/-- The span attached to an identity subdivision morphism is isomorphic to
the identity span. -/
noncomputable def admissibleMonoSubdivisionQuillenSpanIdIso
    (x : AdmissibleMonoSubdivision (C := C)) :
    admissibleMonoSubdivisionQuillenSpan (𝟙 x) ≅
      (Span.id (c := admissibleMonoSubdivisionQuotient x) :
        QuillenSpan (admissibleMonoSubdivisionQuotient x)
          (admissibleMonoSubdivisionQuotient x)) := by
  let _ := admissibleMonoSubdivisionQuillenSpan_id_l_isIso x
  refine Span.mkIso
    (asIso (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).l) ?_ ?_
  · simp
  · change
      (asIso (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).l).hom ≫
          𝟙 (admissibleMonoSubdivisionQuotient x) =
        (admissibleMonoSubdivisionQuillenSpan (𝟙 x)).r
    rw [asIso_hom, Category.comp_id,
      admissibleMonoSubdivisionQuillenSpan_id_l_eq_r]

/-- The quotient-level Quillen morphism attached to an identity
subdivision morphism is the identity. -/
@[simp]
theorem admissibleMonoSubdivisionQuillenHom_id
    (x : AdmissibleMonoSubdivision (C := C)) :
    admissibleMonoSubdivisionQuillenHom (𝟙 x) =
      𝟙 (admissibleMonoSubdivisionQuillenObj x) := by
  unfold admissibleMonoSubdivisionQuillenHom
  rw [← mkHom_id]
  exact QuillenQ.mkHom_sound
    (admissibleMonoSubdivisionQuillenSpanIdIso x)

end AlgebraicKTheory

end
