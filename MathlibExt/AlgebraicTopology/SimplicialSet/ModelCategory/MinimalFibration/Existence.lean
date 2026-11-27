/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Equivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationHomotopyExtension
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationPathComposition
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexAttachmentCompat
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.Order.Zorn

/-!
# Existence of minimal deformation subfibrations

Every Kan fibration p:E→B contains a minimal subfibration M→B whose inclusion M→E is a strong
deformation retract. Its deformation is stationary on M and keeps the projection to B fixed.

Choose separated representatives for fiberwise simplex-homotopy classes, retaining every
degenerate simplex. The core is the largest subcomplex whose simplices are selected
representatives. Maximal compatible deformation stages expand to all E and yield the required
retraction, deformation and minimal fibration. All objects may lie in any simplicial-set
universe u.
-/

@[expose] public section

noncomputable section

open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Opposite
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet
namespace MinimalFibration

variable {E B : SSet.{u}} {p : E ⟶ B}

/-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M and
over B, and minimal Kan fibration p restricted to M. The retraction satisfies ι≫r=id_M and the
deformation runs from id_E to r≫ι. -/
structure MinimalSubfibration (p : E ⟶ B) where
  /-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M
and over B, and minimal Kan fibration p restricted to M. The carrier is the simplicial
subcomplex M of E. -/
  carrier : E.Subcomplex
  /-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M
and over B, and minimal Kan fibration p restricted to M. The strong deformation retract has
retraction r and homotopy id_E→r≫ι fixed on the subcomplex M. -/
  sdr : StrongDeformationRetract carrier.ι
  /-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M
and over B, and minimal Kan fibration p restricted to M. Its cylinder H:E×Δ[1]→E satisfies
H≫p=pr₁≫p, so the deformation keeps every base value fixed. -/
  over : sdr.homotopy.h ≫ p = fst E (Δ[1] : SSet.{u}) ≫ p
  /-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M
and over B, and minimal Kan fibration p restricted to M. The restricted map M→B has horn
lifting and identifies fiberwise homotopic simplices with the same base and boundary. -/
  isMinimalFibration : IsMinimalFibration (carrier.ι ≫ p)

namespace MinimalSubfibration

/-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M and
over B, and minimal Kan fibration p restricted to M. Its deformation is the map-level fiberwise
homotopy over p from id_E to the retract projection r≫ι. -/
def fiberwiseHomotopy (M : MinimalSubfibration p) :
    SSet.FiberwiseHomotopy p p (𝟙 E) (M.sdr.r ≫ M.carrier.ι) where
  hom := M.sdr.homotopy.toHomotopy
  over := M.over

/-- For a simplicial map p:E→B, a minimal subfibration consists of a subcomplex M⊆E, a strong
deformation retract with retraction r:E→M and inclusion ι:M→E, a deformation stationary on M and
over B, and minimal Kan fibration p restricted to M. The restricted arrow M→B is a retract of
p:E→B in the arrow category, with total-space maps ι,r and identity on B. -/
def retractArrow (M : MinimalSubfibration p) :
    RetractArrow (M.carrier.ι ≫ p) p where
  i := Arrow.homMk M.carrier.ι (𝟙 B) (by simp)
  r := Arrow.homMk M.sdr.r (𝟙 B) (by
    calc
      M.sdr.r ≫ (M.carrier.ι ≫ p) =
          (M.sdr.r ≫ M.carrier.ι) ≫ p := (Category.assoc _ _ _).symm
      _ = p := M.fiberwiseHomotopy.fac₁
      _ = p ≫ 𝟙 B := (Category.comp_id _).symm)
  retract := by
    apply Arrow.hom_ext
    · exact M.sdr.retract
    · simp

end MinimalSubfibration

/-!
## Representatives of fiberwise simplex homotopy

For a Kan fibration p:E→B, the boundary-relative fiberwise relation is an equivalence relation
in each degree. Select every degenerate simplex and one representative for each remaining class.
Selected representatives in the same class are equal.
-/

private def simplexSetoid (p : E ⟶ B) [Fibration p] (n : ℕ) :
    Setoid (E _⦋n⦌) where
  r := FiberwiseHomotopic (n := n) p
  iseqv := FiberwiseHomotopic.equivalence p n

private abbrev SimplexClass (p : E ⟶ B) [Fibration p] (n : ℕ) :=
  Quotient (simplexSetoid p n)

private def classHasDegenerate (p : E ⟶ B) [Fibration p]
    {n : ℕ} (q : SimplexClass p n) : Prop :=
  ∃ x : E _⦋n⦌, x ∈ E.degenerate n ∧
    Quotient.mk (simplexSetoid p n) x = q

private noncomputable def selectedSet (p : E ⟶ B) [Fibration p]
    (n : ℕ) : Set (E _⦋n⦌) :=
  E.degenerate n ∪
    Set.range (fun q : {q : SimplexClass p n // ¬ classHasDegenerate p q} ↦
      q.1.out)

private lemma degenerate_subset_selectedSet
    (p : E ⟶ B) [Fibration p] (n : ℕ) :
    E.degenerate n ⊆ selectedSet p n :=
  fun _ hx ↦ Or.inl hx

private lemma exists_selected_related
    (p : E ⟶ B) [Fibration p] {n : ℕ} (x : E _⦋n⦌) :
    ∃ y, y ∈ selectedSet p n ∧ FiberwiseHomotopic p x y := by
  let q : SimplexClass p n := Quotient.mk (simplexSetoid p n) x
  by_cases hq : classHasDegenerate p q
  · obtain ⟨d, hd, hdq⟩ := hq
    refine ⟨d, Or.inl hd, ?_⟩
    have hdx : FiberwiseHomotopic p d x :=
      Quotient.exact (by simpa [q] using hdq)
    exact (FiberwiseHomotopic.equivalence p n).symm hdx
  · refine ⟨q.out, Or.inr ⟨⟨q, hq⟩, rfl⟩, ?_⟩
    have hqx : FiberwiseHomotopic p q.out x :=
      Quotient.exact (show Quotient.mk (simplexSetoid p n) q.out =
        Quotient.mk (simplexSetoid p n) x from q.out_eq)
    exact (FiberwiseHomotopic.equivalence p n).symm hqx

private lemma selected_related_unique
    (p : E ⟶ B) [Fibration p] {n : ℕ} {x y : E _⦋n⦌}
    (hx : x ∈ selectedSet p n) (hy : y ∈ selectedSet p n)
    (hxy : FiberwiseHomotopic p x y) : x = y := by
  rcases hx with hx | ⟨q, rfl⟩
  · rcases hy with hy | ⟨r, rfl⟩
    · obtain ⟨H⟩ := hxy
      exact H.eq_of_degenerate hx hy
    · exfalso
      exact r.2 ⟨x, hx, (Quotient.sound hxy).trans r.1.out_eq⟩
  · rcases hy with hy | ⟨r, rfl⟩
    · exfalso
      exact q.2 ⟨y, hy, (Quotient.sound hxy).symm.trans q.1.out_eq⟩
    · have hqr : q.1 = r.1 :=
        q.1.out_eq.symm.trans ((Quotient.sound hxy).trans r.1.out_eq)
      exact congrArg Quotient.out hqr

private structure RepresentativeSystem (p : E ⟶ B) where
  chosen : ∀ n, Set (E _⦋n⦌)
  containsDegenerate : ∀ n, E.degenerate n ⊆ chosen n
  representative : ∀ {n} (x : E _⦋n⦌),
    ∃ y, y ∈ chosen n ∧ FiberwiseHomotopic p x y
  separated : ∀ {n} {x y : E _⦋n⦌},
    x ∈ chosen n → y ∈ chosen n → FiberwiseHomotopic p x y → x = y

private noncomputable def quotientRepresentativeSystem
    (p : E ⟶ B) [Fibration p] : RepresentativeSystem p where
  chosen := selectedSet p
  containsDegenerate := degenerate_subset_selectedSet p
  representative := exists_selected_related p
  separated := selected_related_unique p

private lemma simplexHomotopy_boundary_eq
    {n : ℕ} {x y : E _⦋n⦌} (H : FiberwiseHomotopy p x y) :
    (boundary n).ι ≫ yonedaEquiv.symm x =
      (boundary n).ι ≫ yonedaEquiv.symm y := by
  ext m ⟨a, ha⟩
  change (yonedaEquiv.symm x).app m a = (yonedaEquiv.symm y).app m a
  rw [← H.h₁]
  symm
  exact H.stationary a ha ((SSet.ι₁.app m a).2)

/-!
## The core contained in the selected representatives

A subcomplex is admissible when all its simplices belong to the degreewise selected sets. The
union of all such subcomplexes is the representative core. It is admissible and contains every
admissible subcomplex.
-/

namespace RepresentativeSystem

private def Admissible (R : RepresentativeSystem p) (A : E.Subcomplex) : Prop :=
  ∀ (n : ℕ) (x : E _⦋n⦌), x ∈ A.obj (op ⦋n⦌) → x ∈ R.chosen n

private noncomputable def core (R : RepresentativeSystem p) : E.Subcomplex :=
  sSup {A : E.Subcomplex | R.Admissible A}

private lemma core_admissible (R : RepresentativeSystem p) :
    R.Admissible R.core := by
  intro n x hx
  rw [core, Subfunctor.sSup_obj] at hx
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA⟩ := hx
  exact hA n x hxA

private lemma le_core (R : RepresentativeSystem p) {A : E.Subcomplex}
    (hA : R.Admissible A) : A ≤ R.core :=
  le_sSup hA

private lemma mem_core_of_boundary
    (R : RepresentativeSystem p) {n : ℕ} {x : E _⦋n⦌}
    (hx : x ∈ R.chosen n)
    (d : (boundary n : SSet.{u}) ⟶ (R.core : SSet.{u}))
    (hd : d ≫ R.core.ι = (boundary n).ι ≫ yonedaEquiv.symm x) :
    x ∈ R.core.obj (op ⦋n⦌) := by
  let C : E.Subcomplex := R.core ⊔ Subcomplex.ofSimplex x
  have hC : R.Admissible C := by
    intro m z hz
    rcases hz with hz | hz
    · exact R.core_admissible m z hz
    · rw [Subcomplex.mem_ofSimplex_obj_iff] at hz
      obtain ⟨f, rfl⟩ := hz
      by_cases hdeg : E.map f.op x ∈ E.degenerate m
      · exact R.containsDegenerate m hdeg
      · have hnd : E.map f.op x ∈ E.nonDegenerate m := hdeg
        have hstd :
            (stdSimplex.objEquiv.symm f : (Δ[n] : SSet.{u}) _⦋m⦌) ∈
              (Δ[n] : SSet.{u}).nonDegenerate m :=
          nonDegenerate_of_app_apply (yonedaEquiv.symm x) hnd
        have : Mono f :=
          (stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono f).mp hstd
        have hmn : m ≤ n := SimplexCategory.len_le_of_mono f
        obtain hlt | rfl := hmn.lt_or_eq
        · have hmem : (stdSimplex.objEquiv.symm f : (Δ[n] : SSet.{u}) _⦋m⦌) ∈
              (boundary n).obj (op ⦋m⦌) := by
            rw [boundary_obj_eq_univ m n hlt]
            trivial
          have happ := ConcreteCategory.congr_hom (congr_app hd (op ⦋m⦌))
            ⟨stdSimplex.objEquiv.symm f, hmem⟩
          apply R.core_admissible m
          change E.map f.op x ∈ R.core.obj (op ⦋m⦌)
          change (d.app _ ⟨stdSimplex.objEquiv.symm f, hmem⟩).1 =
            E.map f.op x at happ
          rw [← happ]
          exact (d.app _ ⟨stdSimplex.objEquiv.symm f, hmem⟩).2
        · have hf : f = 𝟙 _ := SimplexCategory.eq_id_of_mono f
          subst f
          simpa using hx
  have hle : C ≤ R.core := R.le_core hC
  exact hle _ (Or.inr (Subcomplex.mem_ofSimplex_obj x))

end RepresentativeSystem

/-!
## Ordered deformation stages over the base

A stage consists of a subcomplex A containing the core, a retraction A→core and a fiberwise
homotopy from the retract projection to the inclusion A→E, fixed on the core. Stages are ordered
by extension of the carrier and of the homotopy.
-/

private structure Stage (R : RepresentativeSystem p) where
  carrier : E.Subcomplex
  core_le : R.core ≤ carrier
  retract : (carrier : SSet.{u}) ⟶ (R.core : SSet.{u})
  retract_core : Subcomplex.homOfLE core_le ≫ retract =
    𝟙 (R.core : SSet.{u})
  homotopy : SSet.FiberwiseHomotopy
    (carrier.ι ≫ p) p (retract ≫ R.core.ι) carrier.ι
  stationary :
    (Subcomplex.homOfLE core_le ▷ (Δ[1] : SSet.{u})) ≫ homotopy.hom.h =
      fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.core.ι

namespace Stage

private structure Hom {R : RepresentativeSystem p} (a b : Stage R) : Prop where
  carrier_le : a.carrier ≤ b.carrier
  homotopy_restrict :
    a.homotopy.hom.h =
      (Subcomplex.homOfLE carrier_le ▷ (Δ[1] : SSet.{u})) ≫
        b.homotopy.hom.h

private instance {R : RepresentativeSystem p} : LE (Stage R) := ⟨Hom⟩

private instance {R : RepresentativeSystem p} : PartialOrder (Stage R) where
  le_refl a :=
    { carrier_le := le_rfl
      homotopy_restrict := by simp }
  le_trans a b c hab hbc :=
    { carrier_le := hab.carrier_le.trans hbc.carrier_le
      homotopy_restrict := by
        rw [hab.homotopy_restrict, hbc.homotopy_restrict,
          ← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
          Subcomplex.homOfLE_comp] }
  le_antisymm a b hab hba := by
    rcases a with ⟨A, hMA, rA, hrA, HA, hsA⟩
    rcases b with ⟨B', hMB, rB, hrB, HB, hsB⟩
    have hAB : A = B' := le_antisymm hab.carrier_le hba.carrier_le
    subst B'
    have hH : HA.hom.h = HB.hom.h := by
      simpa using hab.homotopy_restrict
    have hr : rA = rB := by
      apply (cancel_mono R.core.ι).mp
      rw [← HA.hom.h₀, ← HB.hom.h₀, hH]
    subst rB
    have hHom : HA.hom = HB.hom := by
      exact SSet.RelativeMorphism.Homotopy.ext hH
    have hFH : HA = HB := by
      cases HA
      cases HB
      cases hHom
      rfl
    subst HB
    congr

private lemma retract_naturality {R : RepresentativeSystem p}
    {a b : Stage R} (h : a ≤ b) :
    Subcomplex.homOfLE h.carrier_le ≫ b.retract = a.retract := by
  apply (cancel_mono R.core.ι).mp
  rw [Category.assoc, ← b.homotopy.hom.h₀, ← a.homotopy.hom.h₀,
    h.homotopy_restrict]
  simp

private noncomputable def bottom (R : RepresentativeSystem p) : Stage R where
  carrier := R.core
  core_le := le_rfl
  retract := 𝟙 _
  retract_core := by simp
  homotopy := SSet.FiberwiseHomotopy.refl R.core.ι (by simp)
  stationary := by
    simp [SSet.FiberwiseHomotopy.refl]

private instance {R : RepresentativeSystem p} : OrderBot (Stage R) where
  bot := bottom R
  bot_le a :=
    { carrier_le := a.core_le
      homotopy_restrict := by
        simpa [bottom, SSet.FiberwiseHomotopy.refl] using a.stationary.symm }

private lemma carrierMonotone {R : RepresentativeSystem p} :
    Monotone (Stage.carrier : Stage R → E.Subcomplex) :=
  fun _ _ h ↦ h.carrier_le

end Stage

set_option linter.style.haveILetI false in
private theorem stages_chain_bddAbove {R : RepresentativeSystem p}
    (c : Set (Stage R)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : BddAbove c := by
  classical
  letI : Nonempty c := Set.nonempty_coe_sort.mpr hne
  letI : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  letI : IsFiltered c := inferInstance
  let F : c ⥤ E.Subcomplex :=
    (show Monotone (fun j : c ↦ j.1.carrier) from
      fun _ _ h ↦ h.carrier_le).functor
  let Ainf : E.Subcomplex := ⨆ j : c, j.1.carrier
  let latticeCocone :=
    Preorder.colimitCoconeOfIsLUB F (pt := Ainf) (by
      dsimp [F, Ainf]
      exact isLUB_iSup)
  let carrierCocone : Cocone (F ⋙ Subcomplex.toSSetFunctor) :=
    { pt := Ainf
      ι :=
        { app := fun j ↦
            Subcomplex.homOfLE (le_iSup (fun k : c ↦ k.1.carrier) j)
          naturality := by
            intro j k f
            have hjk : j.1 ≤ k.1 := leOfHom f
            change Subcomplex.homOfLE hjk.carrier_le ≫
                Subcomplex.homOfLE (le_iSup (fun l : c ↦ l.1.carrier) k) =
              Subcomplex.homOfLE (le_iSup (fun l : c ↦ l.1.carrier) j) ≫
                𝟙 (Ainf : SSet.{u})
            rw [Subcomplex.homOfLE_comp, Category.comp_id] } }
  have hcA : IsColimit carrierCocone := by
    change IsColimit
      (Subcomplex.toSSetFunctor.mapCocone latticeCocone.cocone)
    exact isColimitOfPreserves Subcomplex.toSSetFunctor latticeCocone.isColimit
  let cylinderCocone :=
    (MonoidalCategory.tensorRight (Δ[1] : SSet.{u})).mapCocone carrierCocone
  have hcAI : IsColimit cylinderCocone :=
    isColimitOfPreserves
      (MonoidalCategory.tensorRight (Δ[1] : SSet.{u})) hcA
  have hcylinderLeg (j : c) :
      cylinderCocone.ι.app j =
        (carrierCocone.ι.app j ▷ (Δ[1] : SSet.{u})) := by
    rfl
  let retractCocone : Cocone (F ⋙ Subcomplex.toSSetFunctor) :=
    { pt := R.core
      ι :=
        { app := fun j ↦ j.1.retract
          naturality := by
            intro j k f
            have hjk : j.1 ≤ k.1 := leOfHom f
            change Subcomplex.homOfLE hjk.carrier_le ≫ k.1.retract =
              j.1.retract ≫ 𝟙 (R.core : SSet.{u})
            simpa only [Category.comp_id] using
              Stage.retract_naturality (R := R) hjk } }
  let rInf : (Ainf : SSet.{u}) ⟶ (R.core : SSet.{u}) :=
    hcA.desc retractCocone
  have hrInf_fac (j : c) : carrierCocone.ι.app j ≫ rInf = j.1.retract := by
    exact hcA.fac retractCocone j
  let homotopyCocone :
      Cocone ((F ⋙ Subcomplex.toSSetFunctor) ⋙
        MonoidalCategory.tensorRight (Δ[1] : SSet.{u})) :=
    { pt := E
      ι :=
        { app := fun j ↦ j.1.homotopy.hom.h
          naturality := by
            intro j k f
            have hjk : j.1 ≤ k.1 := leOfHom f
            change (Subcomplex.homOfLE hjk.carrier_le ▷
                (Δ[1] : SSet.{u})) ≫ k.1.homotopy.hom.h =
              j.1.homotopy.hom.h ≫ 𝟙 E
            simpa only [Category.comp_id] using hjk.homotopy_restrict.symm } }
  let HInf : (Ainf : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E :=
    hcAI.desc homotopyCocone
  have hHInf_fac (j : c) :
      cylinderCocone.ι.app j ≫ HInf = j.1.homotopy.hom.h := by
    exact hcAI.fac homotopyCocone j
  have hrInf_fac' (j : c) :
      Subcomplex.homOfLE (le_iSup (fun k : c ↦ k.1.carrier) j) ≫ rInf =
        j.1.retract := by
    change carrierCocone.ι.app j ≫ rInf = j.1.retract
    exact hrInf_fac j
  have hHInf_fac' (j : c) :
      (Subcomplex.homOfLE (le_iSup (fun k : c ↦ k.1.carrier) j) ▷
          (Δ[1] : SSet.{u})) ≫ HInf = j.1.homotopy.hom.h := by
    change (carrierCocone.ι.app j ▷ (Δ[1] : SSet.{u})) ≫ HInf = _
    rw [← hcylinderLeg]
    exact hHInf_fac j
  let j₀ : c := Classical.choice inferInstance
  have hcore : R.core ≤ Ainf :=
    j₀.1.core_le.trans (le_iSup (fun j : c ↦ j.1.carrier) j₀)
  have hcore_factor :
      Subcomplex.homOfLE hcore =
        Subcomplex.homOfLE j₀.1.core_le ≫
          Subcomplex.homOfLE (le_iSup (fun j : c ↦ j.1.carrier) j₀) := by
    simpa using (Subcomplex.homOfLE_comp j₀.1.core_le
      (le_iSup (fun j : c ↦ j.1.carrier) j₀)).symm
  have hretractCore :
      Subcomplex.homOfLE hcore ≫ rInf = 𝟙 (R.core : SSet.{u}) := by
    rw [hcore_factor, Category.assoc, hrInf_fac',
      j₀.1.retract_core]
  have hzero : SSet.ι₀ ≫ HInf = rInf ≫ R.core.ι := by
    apply hcA.hom_ext
    intro j
    have hj : j.1.carrier ≤ Ainf :=
      le_iSup (fun k : c ↦ k.1.carrier) j
    change Subcomplex.homOfLE hj ≫ (SSet.ι₀ ≫ HInf) =
      Subcomplex.homOfLE hj ≫ (rInf ≫ R.core.ι)
    calc
      Subcomplex.homOfLE hj ≫ (SSet.ι₀ ≫ HInf) =
          (Subcomplex.homOfLE hj ≫ SSet.ι₀) ≫ HInf :=
        (Category.assoc _ _ _).symm
      _ = (SSet.ι₀ ≫ (Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u}))) ≫
          HInf := by rw [SSet.ι₀_comp]
      _ = SSet.ι₀ ≫ ((Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫
          HInf) := Category.assoc _ _ _
      _ = SSet.ι₀ ≫ j.1.homotopy.hom.h := by rw [hHInf_fac']
      _ = j.1.retract ≫ R.core.ι := j.1.homotopy.hom.h₀
      _ = (Subcomplex.homOfLE hj ≫ rInf) ≫ R.core.ι := by
        rw [hrInf_fac']
      _ = Subcomplex.homOfLE hj ≫ (rInf ≫ R.core.ι) :=
        Category.assoc _ _ _
  have hone : SSet.ι₁ ≫ HInf = Ainf.ι := by
    apply hcA.hom_ext
    intro j
    have hj : j.1.carrier ≤ Ainf :=
      le_iSup (fun k : c ↦ k.1.carrier) j
    change Subcomplex.homOfLE hj ≫ (SSet.ι₁ ≫ HInf) =
      Subcomplex.homOfLE hj ≫ Ainf.ι
    calc
      Subcomplex.homOfLE hj ≫ (SSet.ι₁ ≫ HInf) =
          (Subcomplex.homOfLE hj ≫ SSet.ι₁) ≫ HInf :=
        (Category.assoc _ _ _).symm
      _ = (SSet.ι₁ ≫ (Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u}))) ≫
          HInf := by rw [SSet.ι₁_comp]
      _ = SSet.ι₁ ≫ ((Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫
          HInf) := Category.assoc _ _ _
      _ = SSet.ι₁ ≫ j.1.homotopy.hom.h := by rw [hHInf_fac']
      _ = j.1.carrier.ι := j.1.homotopy.hom.h₁
      _ = Subcomplex.homOfLE hj ≫ Ainf.ι :=
        (Subcomplex.homOfLE_ι hj).symm
  have hover : HInf ≫ p =
      fst (Ainf : SSet.{u}) (Δ[1] : SSet.{u}) ≫ Ainf.ι ≫ p := by
    apply hcAI.hom_ext
    intro j
    rw [hcylinderLeg]
    have hj : j.1.carrier ≤ Ainf :=
      le_iSup (fun k : c ↦ k.1.carrier) j
    change (Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫
      (HInf ≫ p) =
      (Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫
        (fst (Ainf : SSet.{u}) (Δ[1] : SSet.{u}) ≫ Ainf.ι ≫ p)
    calc
      (Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫ (HInf ≫ p) =
          ((Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫ HInf) ≫ p :=
        (Category.assoc _ _ _).symm
      _ = j.1.homotopy.hom.h ≫ p := by rw [hHInf_fac']
      _ = fst (j.1.carrier : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          j.1.carrier.ι ≫ p := j.1.homotopy.over
      _ = ((Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫
          fst (Ainf : SSet.{u}) (Δ[1] : SSet.{u})) ≫ Ainf.ι ≫ p := by
        simp only [CartesianMonoidalCategory.whiskerRight_fst,
          Category.assoc, Subcomplex.homOfLE_ι_assoc]
      _ = (Subcomplex.homOfLE hj ▷ (Δ[1] : SSet.{u})) ≫
          (fst (Ainf : SSet.{u}) (Δ[1] : SSet.{u}) ≫ Ainf.ι ≫ p) := by
        simp only [Category.assoc]
  have hstationary :
      (Subcomplex.homOfLE hcore ▷ (Δ[1] : SSet.{u})) ≫ HInf =
        fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.core.ι := by
    rw [hcore_factor, MonoidalCategory.comp_whiskerRight,
      Category.assoc, hHInf_fac', j₀.1.stationary]
  let upper : Stage R :=
    { carrier := Ainf
      core_le := hcore
      retract := rInf
      retract_core := hretractCore
      homotopy :=
        { hom :=
            { h := HInf
              h₀ := hzero
              h₁ := hone
              rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx }
          over := hover }
      stationary := hstationary }
  refine ⟨upper, ?_⟩
  intro a ha
  let j : c := ⟨a, ha⟩
  refine
    { carrier_le := le_iSup (fun k : c ↦ k.1.carrier) j
      homotopy_restrict := ?_ }
  change a.homotopy.hom.h =
    (carrierCocone.ι.app j ▷ (Δ[1] : SSet.{u})) ≫ HInf
  rw [← hcylinderLeg, hHInf_fac]

set_option linter.style.haveILetI false in
private theorem exists_maximalStage (R : RepresentativeSystem p) :
    ∃ a : Stage R, IsMax a := by
  letI : Nonempty (Stage R) := ⟨⊥⟩
  exact zorn_le_nonempty stages_chain_bddAbove

/-!
## Adjoining a missing simplex

A simplex of minimal missing dimension has its boundary in the current stage. Fibration homotopy
extension and its selected representative extend the retraction and deformation after adjoining
that simplex.
-/

private structure AttachmentData {R : RepresentativeSystem p}
    (a : Stage R) (A' : E.Subcomplex) (n : ℕ)
    (t : (boundary n : SSet.{u}) ⟶ (a.carrier : SSet.{u}))
    (b : Δ[n] ⟶ (A' : SSet.{u})) where
  alpha : Δ[n] ⊗ Δ[1] ⟶ E
  beta : Δ[n] ⟶ (R.core : SSet.{u})
  boundary_beta : (boundary n).ι ≫ beta = t ≫ a.retract
  boundary_alpha :
    ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ alpha =
      (t ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h
  alpha_zero : SSet.ι₀ ≫ alpha = beta ≫ R.core.ι
  alpha_one : SSet.ι₁ ≫ alpha = b ≫ A'.ι
  alpha_over : alpha ≫ p =
    fst Δ[n] (Δ[1] : SSet.{u}) ≫ b ≫ A'.ι ≫ p

set_option linter.style.haveILetI false in
private theorem exists_attachmentData {R : RepresentativeSystem p}
    [Fibration p] (a : Stage R) (A' : E.Subcomplex)
    (lt : a.carrier < A') (n : ℕ)
    (t : (boundary n : SSet.{u}) ⟶ (a.carrier : SSet.{u}))
    (b : Δ[n] ⟶ (A' : SSet.{u}))
    (w : IsPushout t (boundary n).ι
      (Subcomplex.homOfLE lt.le) b) :
    Nonempty (AttachmentData a A' n t b) := by
  classical
  let hE : (boundary n : SSet.{u}) ⊗ Δ[1] ⟶ E :=
    (t ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h
  let f : Δ[n] ⟶ E := b ≫ A'.ι
  let hB : Δ[n] ⊗ Δ[1] ⟶ B :=
    fst Δ[n] (Δ[1] : SSet.{u}) ≫ b ≫ A'.ι ≫ p
  have hEndpoint : (boundary n).ι ≫ f = SSet.ι₁ ≫ hE := by
    dsimp [f, hE]
    calc
      (boundary n).ι ≫ b ≫ A'.ι =
          (t ≫ Subcomplex.homOfLE lt.le) ≫ A'.ι := by
        rw [← Category.assoc, w.w]
      _ = t ≫ a.carrier.ι := by
        rw [Category.assoc, Subcomplex.homOfLE_ι]
      _ = t ≫ (SSet.ι₁ ≫ a.homotopy.hom.h) := by
        rw [a.homotopy.hom.h₁]
      _ = (t ≫ SSet.ι₁) ≫ a.homotopy.hom.h :=
        (Category.assoc _ _ _).symm
      _ = (SSet.ι₁ ≫ (t ▷ (Δ[1] : SSet.{u}))) ≫
          a.homotopy.hom.h := by rw [SSet.ι₁_comp]
      _ = SSet.ι₁ ≫ ((t ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h) := Category.assoc _ _ _
  have hBaseEndpoint : SSet.ι₁ ≫ hB = f ≫ p := by
    dsimp [hB, f]
    simp only [Category.assoc, SSet.ι₁_fst_assoc]
  have hBoundaryBase :
      ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ hB = hE ≫ p := by
    dsimp [hB, hE]
    calc
      ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫
          (fst Δ[n] (Δ[1] : SSet.{u}) ≫ b ≫ A'.ι ≫ p) =
        fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          (boundary n).ι ≫ b ≫ A'.ι ≫ p := by
            simp only [CartesianMonoidalCategory.whiskerRight_fst_assoc]
      _ = fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          t ≫ a.carrier.ι ≫ p := by
            rw [← w.w_assoc]
            simp only [Subcomplex.homOfLE_ι_assoc]
      _ = (t ▷ (Δ[1] : SSet.{u})) ≫
          (fst (a.carrier : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            a.carrier.ι ≫ p) := by
              simp only [CartesianMonoidalCategory.whiskerRight_fst_assoc]
      _ = (t ▷ (Δ[1] : SSet.{u})) ≫
          (a.homotopy.hom.h ≫ p) := by rw [a.homotopy.over]
      _ = ((t ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h) ≫ p :=
        (Category.assoc _ _ _).symm
  obtain ⟨psi, hpsiOne, hpsiBoundary, hpsiOver⟩ :=
    homotopy_extension_property₁ (boundary n).ι p hE f hEndpoint hB
      hBaseEndpoint hBoundaryBase
  let x : E _⦋n⦌ := yonedaEquiv (SSet.ι₀ ≫ psi)
  obtain ⟨y, hySelected, hxy⟩ := R.representative x
  obtain ⟨rho⟩ := hxy
  let d : (boundary n : SSet.{u}) ⟶ (R.core : SSet.{u}) :=
    t ≫ a.retract
  have hdx : d ≫ R.core.ι =
      (boundary n).ι ≫ yonedaEquiv.symm x := by
    dsimp [d, x]
    calc
      (t ≫ a.retract) ≫ R.core.ι =
          t ≫ (a.retract ≫ R.core.ι) := Category.assoc _ _ _
      _ = t ≫ (SSet.ι₀ ≫ a.homotopy.hom.h) := by
        rw [a.homotopy.hom.h₀]
      _ = (t ≫ SSet.ι₀) ≫ a.homotopy.hom.h :=
        (Category.assoc _ _ _).symm
      _ = (SSet.ι₀ ≫ (t ▷ (Δ[1] : SSet.{u}))) ≫
          a.homotopy.hom.h := by rw [SSet.ι₀_comp]
      _ = SSet.ι₀ ≫ ((t ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h) := Category.assoc _ _ _
      _ = SSet.ι₀ ≫ (((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ psi) := by
        rw [hpsiBoundary]
      _ = (SSet.ι₀ ≫ ((boundary n).ι ▷ (Δ[1] : SSet.{u}))) ≫ psi :=
        (Category.assoc _ _ _).symm
      _ = ((boundary n).ι ≫ SSet.ι₀) ≫ psi := by
        rw [SSet.ι₀_comp]
      _ = (boundary n).ι ≫ (SSet.ι₀ ≫ psi) := Category.assoc _ _ _
      _ = (boundary n).ι ≫
          yonedaEquiv.symm (yonedaEquiv (SSet.ι₀ ≫ psi)) := by simp
  have hdy : d ≫ R.core.ι =
      (boundary n).ι ≫ yonedaEquiv.symm y :=
    hdx.trans (simplexHomotopy_boundary_eq rho)
  have hyCore : y ∈ R.core.obj (op ⦋n⦌) :=
    R.mem_core_of_boundary hySelected d hdy
  let beta : Δ[n] ⟶ (R.core : SSet.{u}) :=
    yonedaEquiv.symm (⟨y, hyCore⟩ : R.core _⦋n⦌)
  have hbetaBoundary : (boundary n).ι ≫ beta = t ≫ a.retract := by
    apply (cancel_mono R.core.ι).mp
    calc
      ((boundary n).ι ≫ beta) ≫ R.core.ι =
          (boundary n).ι ≫ (beta ≫ R.core.ι) := Category.assoc _ _ _
      _ = (boundary n).ι ≫ yonedaEquiv.symm y := by
        dsimp [beta]
        rw [SSet.yonedaEquiv_symm_comp]
        rfl
      _ = d ≫ R.core.ι := hdy.symm
      _ = (t ≫ a.retract) ≫ R.core.ι := rfl
  let rhoRev : FiberwiseHomotopy p y x := rho.symm
  let q := ihomToPullback (boundary n).ι p
  letI : Fibration q := SSet.fibration_ihomToPullback (boundary n).ι p
  let e01 : Δ[1] ⟶ (ihom Δ[n]).obj E := curry rhoRev.h
  let e12 : Δ[1] ⟶ (ihom Δ[n]).obj E := curry psi
  have hcommon : stdSimplex.δ 0 ≫ e01 = stdSimplex.δ 1 ≫ e12 := by
    dsimp [e01, e12]
    rw [← MonoidalClosed.curry_natural_left,
      ← MonoidalClosed.curry_natural_left]
    apply congrArg MonoidalClosed.curry
    calc
      (Δ[n] ◁ stdSimplex.δ 0) ≫ rhoRev.h =
          ((stdSimplex.rightUnitor Δ[n]).hom ≫ SSet.ι₁) ≫ rhoRev.h := by
        rw [stdSimplex.rightUnitor_hom_ι₁]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫
          (SSet.ι₁ ≫ rhoRev.h) := Category.assoc _ _ _
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫ yonedaEquiv.symm x := by
        rw [rhoRev.h₁]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫ (SSet.ι₀ ≫ psi) := by
        dsimp [x]
        rw [Equiv.symm_apply_apply]
      _ = ((stdSimplex.rightUnitor Δ[n]).hom ≫ SSet.ι₀) ≫ psi :=
        (Category.assoc _ _ _).symm
      _ = (Δ[n] ◁ stdSimplex.δ 1) ≫ psi := by
        rw [stdSimplex.rightUnitor_hom_ι₀]
  let v : ((ihom Δ[n]).obj E) _⦋0⦌ :=
    (ihom₀Equiv Δ[n] E).symm (SSet.ι₀ ≫ psi)
  let q0 := q.app (op ⦋0⦌) v
  have hconstV : (SSet.const (X := (Δ[1] : SSet.{u})) v) =
      curry (fst Δ[n] (Δ[1] : SSet.{u}) ≫ (SSet.ι₀ ≫ psi)) := by
    ext m z
    rfl
  have hpre : e01 ≫ (pre (boundary n).ι).app E =
      SSet.const (X := (Δ[1] : SSet.{u})) v ≫
        (pre (boundary n).ι).app E := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_pre_app,
      MonoidalClosed.uncurry_pre_app]
    dsimp [e01]
    rw [MonoidalClosed.uncurry_curry, hconstV,
      MonoidalClosed.uncurry_curry]
    calc
      ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ rhoRev.h =
          fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (boundary n).ι ≫ yonedaEquiv.symm y :=
        rhoRev.homotopyRel.stationary_eq
      _ = fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (boundary n).ι ≫ yonedaEquiv.symm x := by
        rw [simplexHomotopy_boundary_eq rho]
      _ = fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (boundary n).ι ≫ (SSet.ι₀ ≫ psi) := by
        dsimp [x]
        rw [Equiv.symm_apply_apply]
      _ = ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫
          (fst Δ[n] (Δ[1] : SSet.{u}) ≫ (SSet.ι₀ ≫ psi)) := by
        simp only [CartesianMonoidalCategory.whiskerRight_fst_assoc]
  have hmap : e01 ≫ (ihom Δ[n]).map p =
      SSet.const (X := (Δ[1] : SSet.{u})) v ≫ (ihom Δ[n]).map p := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_right,
      MonoidalClosed.uncurry_natural_right]
    dsimp [e01]
    rw [MonoidalClosed.uncurry_curry, hconstV,
      MonoidalClosed.uncurry_curry]
    calc
      rhoRev.h ≫ p = fst Δ[n] (Δ[1] : SSet.{u}) ≫
          (yonedaEquiv.symm y ≫ p) := rhoRev.over
      _ = fst Δ[n] (Δ[1] : SSet.{u}) ≫
          (yonedaEquiv.symm x ≫ p) := by rw [rhoRev.base_eq]
      _ = fst Δ[n] (Δ[1] : SSet.{u}) ≫
          ((SSet.ι₀ ≫ psi) ≫ p) := by
        dsimp [x]
        rw [Equiv.symm_apply_apply]
      _ = (fst Δ[n] (Δ[1] : SSet.{u}) ≫ (SSet.ι₀ ≫ psi)) ≫ p :=
        (Category.assoc _ _ _).symm
  have hqConst : e01 ≫ q = SSet.const q0 := by
    have hqFst : q ≫
        pullback.fst ((ihom (boundary n : SSet.{u})).map p)
          ((pre (boundary n).ι).app B) =
        (pre (boundary n).ι).app E := by
      dsimp [q, ihomToPullback]
      rw [pullback.lift_fst]
    have hqSnd : q ≫
        pullback.snd ((ihom (boundary n : SSet.{u})).map p)
          ((pre (boundary n).ι).app B) =
        (ihom Δ[n]).map p := by
      dsimp [q, ihomToPullback]
      rw [pullback.lift_snd]
    calc
      e01 ≫ q = SSet.const (X := (Δ[1] : SSet.{u})) v ≫ q := by
        apply pullback.hom_ext
        · calc
            (e01 ≫ q) ≫ pullback.fst _ _ =
                e01 ≫ (q ≫ pullback.fst _ _) := Category.assoc _ _ _
            _ = e01 ≫ (pre (boundary n).ι).app E := by rw [hqFst]
            _ = SSet.const v ≫ (pre (boundary n).ι).app E := hpre
            _ = SSet.const v ≫ (q ≫ pullback.fst _ _) := by rw [hqFst]
            _ = (SSet.const v ≫ q) ≫ pullback.fst _ _ :=
              (Category.assoc _ _ _).symm
        · calc
            (e01 ≫ q) ≫ pullback.snd _ _ =
                e01 ≫ (q ≫ pullback.snd _ _) := Category.assoc _ _ _
            _ = e01 ≫ (ihom Δ[n]).map p := by rw [hqSnd]
            _ = SSet.const v ≫ (ihom Δ[n]).map p := hmap
            _ = SSet.const v ≫ (q ≫ pullback.snd _ _) := by rw [hqSnd]
            _ = (SSet.const v ≫ q) ≫ pullback.snd _ _ :=
              (Category.assoc _ _ _).symm
      _ = SSet.const q0 := by simp [q0]
  obtain ⟨e02, he02Zero, he02One, he02Over⟩ :=
    exists_path_composition_above_of_fibration' q e01 e12 q0 hcommon hqConst
  let alpha : Δ[n] ⊗ Δ[1] ⟶ E := uncurry e02
  have halphaZero : SSet.ι₀ ≫ alpha = beta ≫ R.core.ι := by
    apply (cancel_epi (stdSimplex.rightUnitor Δ[n]).hom).mp
    calc
      (stdSimplex.rightUnitor Δ[n]).hom ≫ (SSet.ι₀ ≫ alpha) =
          (Δ[n] ◁ stdSimplex.δ 1) ≫ alpha := by
        rw [← Category.assoc, stdSimplex.rightUnitor_hom_ι₀]
      _ = uncurry (stdSimplex.δ 1 ≫ e02) := by
        rw [MonoidalClosed.uncurry_natural_left]
      _ = uncurry (stdSimplex.δ 1 ≫ e01) := by rw [he02Zero]
      _ = (Δ[n] ◁ stdSimplex.δ 1) ≫ rhoRev.h := by
        dsimp [e01]
        rw [MonoidalClosed.uncurry_natural_left,
          MonoidalClosed.uncurry_curry]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫ (SSet.ι₀ ≫ rhoRev.h) := by
        rw [← Category.assoc, stdSimplex.rightUnitor_hom_ι₀]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫ yonedaEquiv.symm y := by
        rw [rhoRev.h₀]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫
          (beta ≫ R.core.ι) := by
        dsimp [beta]
        rw [SSet.yonedaEquiv_symm_comp]
        rfl
  have halphaOne : SSet.ι₁ ≫ alpha = b ≫ A'.ι := by
    apply (cancel_epi (stdSimplex.rightUnitor Δ[n]).hom).mp
    calc
      (stdSimplex.rightUnitor Δ[n]).hom ≫ (SSet.ι₁ ≫ alpha) =
          (Δ[n] ◁ stdSimplex.δ 0) ≫ alpha := by
        rw [← Category.assoc, stdSimplex.rightUnitor_hom_ι₁]
      _ = uncurry (stdSimplex.δ 0 ≫ e02) := by
        rw [MonoidalClosed.uncurry_natural_left]
      _ = uncurry (stdSimplex.δ 0 ≫ e12) := by rw [he02One]
      _ = (Δ[n] ◁ stdSimplex.δ 0) ≫ psi := by
        dsimp [e12]
        rw [MonoidalClosed.uncurry_natural_left,
          MonoidalClosed.uncurry_curry]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫ (SSet.ι₁ ≫ psi) := by
        rw [← Category.assoc, stdSimplex.rightUnitor_hom_ι₁]
      _ = (stdSimplex.rightUnitor Δ[n]).hom ≫ (b ≫ A'.ι) := by
        rw [hpsiOne]
  have halphaBoundary :
      ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ alpha =
        (t ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h := by
    have hfst := he02Over =≫
      pullback.fst ((ihom (boundary n : SSet.{u})).map p)
        ((pre (boundary n).ι).app B)
    dsimp [q, ihomToPullback] at hfst
    simp only [Category.assoc, pullback.lift_fst] at hfst
    have huncurry := congrArg MonoidalClosed.uncurry hfst
    have hboundaryPsi :
        ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ alpha =
          ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ psi := by
      simpa [alpha, e12, MonoidalClosed.uncurry_pre_app,
        MonoidalClosed.uncurry_curry] using huncurry
    exact hboundaryPsi.trans (by simpa [hE] using hpsiBoundary)
  have halphaOver : alpha ≫ p =
      fst Δ[n] (Δ[1] : SSet.{u}) ≫ b ≫ A'.ι ≫ p := by
    have hsnd := he02Over =≫
      pullback.snd ((ihom (boundary n : SSet.{u})).map p)
        ((pre (boundary n).ι).app B)
    dsimp [q, ihomToPullback] at hsnd
    simp only [Category.assoc, pullback.lift_snd] at hsnd
    have huncurry := congrArg MonoidalClosed.uncurry hsnd
    simpa [alpha, e12, MonoidalClosed.uncurry_natural_right,
      MonoidalClosed.uncurry_curry, hpsiOver] using huncurry
  exact ⟨{
    alpha := alpha
    beta := beta
    boundary_beta := hbetaBoundary
    boundary_alpha := halphaBoundary
    alpha_zero := halphaZero
    alpha_one := halphaOne
    alpha_over := halphaOver }⟩

private noncomputable def Stage.extend {R : RepresentativeSystem p}
    (a : Stage R) (A' : E.Subcomplex) (lt : a.carrier < A')
    (n : ℕ) (t : (boundary n : SSet.{u}) ⟶ (a.carrier : SSet.{u}))
    (b : Δ[n] ⟶ (A' : SSet.{u}))
    (w : IsPushout t (boundary n).ι (Subcomplex.homOfLE lt.le) b)
    (d : AttachmentData a A' n t b) : Stage R := by
  let wI := w.map (MonoidalCategory.tensorRight (Δ[1] : SSet.{u}))
  let H' : (A' : SSet.{u}) ⊗ Δ[1] ⟶ E :=
    wI.desc a.homotopy.hom.h d.alpha d.boundary_alpha.symm
  have hHOld :
      (Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫ H' =
        a.homotopy.hom.h :=
    wI.inl_desc _ _ _
  have hHNew : (b ▷ (Δ[1] : SSet.{u})) ≫ H' = d.alpha :=
    wI.inr_desc _ _ _
  let r' : (A' : SSet.{u}) ⟶ (R.core : SSet.{u}) :=
    w.desc a.retract d.beta d.boundary_beta.symm
  have hrOld : Subcomplex.homOfLE lt.le ≫ r' = a.retract :=
    w.inl_desc _ _ _
  have hrNew : b ≫ r' = d.beta :=
    w.inr_desc _ _ _
  have hcore : R.core ≤ A' := a.core_le.trans lt.le
  have hrCore : Subcomplex.homOfLE hcore ≫ r' =
      𝟙 (R.core : SSet.{u}) := by
    calc
      Subcomplex.homOfLE hcore ≫ r' =
          (Subcomplex.homOfLE a.core_le ≫
            Subcomplex.homOfLE lt.le) ≫ r' := by
        rw [Subcomplex.homOfLE_comp]
      _ = Subcomplex.homOfLE a.core_le ≫
          (Subcomplex.homOfLE lt.le ≫ r') := Category.assoc _ _ _
      _ = Subcomplex.homOfLE a.core_le ≫ a.retract := by rw [hrOld]
      _ = 𝟙 (R.core : SSet.{u}) := a.retract_core
  have hzero : SSet.ι₀ ≫ H' = r' ≫ R.core.ι := by
    apply w.hom_ext
    · calc
        Subcomplex.homOfLE lt.le ≫ (SSet.ι₀ ≫ H') =
            (Subcomplex.homOfLE lt.le ≫ SSet.ι₀) ≫ H' :=
          (Category.assoc _ _ _).symm
        _ = (SSet.ι₀ ≫ (Subcomplex.homOfLE lt.le ▷
            (Δ[1] : SSet.{u}))) ≫ H' := by rw [SSet.ι₀_comp]
        _ = SSet.ι₀ ≫ ((Subcomplex.homOfLE lt.le ▷
            (Δ[1] : SSet.{u})) ≫ H') := Category.assoc _ _ _
        _ = SSet.ι₀ ≫ a.homotopy.hom.h := by rw [hHOld]
        _ = a.retract ≫ R.core.ι := a.homotopy.hom.h₀
        _ = (Subcomplex.homOfLE lt.le ≫ r') ≫ R.core.ι := by rw [hrOld]
        _ = Subcomplex.homOfLE lt.le ≫ (r' ≫ R.core.ι) :=
          Category.assoc _ _ _
    · calc
        b ≫ (SSet.ι₀ ≫ H') = (b ≫ SSet.ι₀) ≫ H' :=
          (Category.assoc _ _ _).symm
        _ = (SSet.ι₀ ≫ (b ▷ (Δ[1] : SSet.{u}))) ≫ H' := by
          rw [SSet.ι₀_comp]
        _ = SSet.ι₀ ≫ ((b ▷ (Δ[1] : SSet.{u})) ≫ H') :=
          Category.assoc _ _ _
        _ = SSet.ι₀ ≫ d.alpha := by rw [hHNew]
        _ = d.beta ≫ R.core.ι := d.alpha_zero
        _ = (b ≫ r') ≫ R.core.ι := by rw [hrNew]
        _ = b ≫ (r' ≫ R.core.ι) := Category.assoc _ _ _
  have hone : SSet.ι₁ ≫ H' = A'.ι := by
    apply w.hom_ext
    · calc
        Subcomplex.homOfLE lt.le ≫ (SSet.ι₁ ≫ H') =
            (Subcomplex.homOfLE lt.le ≫ SSet.ι₁) ≫ H' :=
          (Category.assoc _ _ _).symm
        _ = (SSet.ι₁ ≫ (Subcomplex.homOfLE lt.le ▷
            (Δ[1] : SSet.{u}))) ≫ H' := by rw [SSet.ι₁_comp]
        _ = SSet.ι₁ ≫ ((Subcomplex.homOfLE lt.le ▷
            (Δ[1] : SSet.{u})) ≫ H') := Category.assoc _ _ _
        _ = SSet.ι₁ ≫ a.homotopy.hom.h := by rw [hHOld]
        _ = a.carrier.ι := a.homotopy.hom.h₁
        _ = Subcomplex.homOfLE lt.le ≫ A'.ι :=
          (Subcomplex.homOfLE_ι lt.le).symm
    · calc
        b ≫ (SSet.ι₁ ≫ H') = (b ≫ SSet.ι₁) ≫ H' :=
          (Category.assoc _ _ _).symm
        _ = (SSet.ι₁ ≫ (b ▷ (Δ[1] : SSet.{u}))) ≫ H' := by
          rw [SSet.ι₁_comp]
        _ = SSet.ι₁ ≫ ((b ▷ (Δ[1] : SSet.{u})) ≫ H') :=
          Category.assoc _ _ _
        _ = SSet.ι₁ ≫ d.alpha := by rw [hHNew]
        _ = b ≫ A'.ι := d.alpha_one
  have hover : H' ≫ p =
      fst (A' : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A'.ι ≫ p := by
    apply wI.hom_ext
    · calc
        (Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫ (H' ≫ p) =
            ((Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫ H') ≫ p :=
          (Category.assoc _ _ _).symm
        _ = a.homotopy.hom.h ≫ p := by rw [hHOld]
        _ = fst (a.carrier : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            a.carrier.ι ≫ p := a.homotopy.over
        _ = ((Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫
            fst (A' : SSet.{u}) (Δ[1] : SSet.{u})) ≫ A'.ι ≫ p := by
          simp only [CartesianMonoidalCategory.whiskerRight_fst,
            Category.assoc, Subcomplex.homOfLE_ι_assoc]
        _ = (Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫
            (fst (A' : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A'.ι ≫ p) := by
          simp only [Category.assoc]
    · calc
        (b ▷ (Δ[1] : SSet.{u})) ≫ (H' ≫ p) =
            ((b ▷ (Δ[1] : SSet.{u})) ≫ H') ≫ p :=
          (Category.assoc _ _ _).symm
        _ = d.alpha ≫ p := by rw [hHNew]
        _ = fst Δ[n] (Δ[1] : SSet.{u}) ≫ b ≫ A'.ι ≫ p :=
          d.alpha_over
        _ = ((b ▷ (Δ[1] : SSet.{u})) ≫
            fst (A' : SSet.{u}) (Δ[1] : SSet.{u})) ≫ A'.ι ≫ p := by
          simp only [CartesianMonoidalCategory.whiskerRight_fst,
            Category.assoc]
        _ = (b ▷ (Δ[1] : SSet.{u})) ≫
            (fst (A' : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A'.ι ≫ p) := by
          simp only [Category.assoc]
  have hstationary :
      (Subcomplex.homOfLE hcore ▷ (Δ[1] : SSet.{u})) ≫ H' =
        fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.core.ι := by
    calc
      (Subcomplex.homOfLE hcore ▷ (Δ[1] : SSet.{u})) ≫ H' =
          ((Subcomplex.homOfLE a.core_le ≫
            Subcomplex.homOfLE lt.le) ▷ (Δ[1] : SSet.{u})) ≫ H' := by
        rw [Subcomplex.homOfLE_comp]
      _ = (Subcomplex.homOfLE a.core_le ▷ (Δ[1] : SSet.{u})) ≫
          ((Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫ H') := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (Subcomplex.homOfLE a.core_le ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h := by rw [hHOld]
      _ = fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.core.ι :=
        a.stationary
  exact
    { carrier := A'
      core_le := hcore
      retract := r'
      retract_core := hrCore
      homotopy :=
        { hom :=
            { h := H'
              h₀ := hzero
              h₁ := hone
              rel := by ext m ⟨⟨x, hx⟩, s⟩; cases hx }
          over := hover }
      stationary := hstationary }

private lemma Stage.lt_extend {R : RepresentativeSystem p}
    (a : Stage R) (A' : E.Subcomplex) (lt : a.carrier < A')
    (n : ℕ) (t : (boundary n : SSet.{u}) ⟶ (a.carrier : SSet.{u}))
    (b : Δ[n] ⟶ (A' : SSet.{u}))
    (w : IsPushout t (boundary n).ι (Subcomplex.homOfLE lt.le) b)
    (d : AttachmentData a A' n t b) :
    a < a.extend A' lt n t b w d := by
  let wI := w.map (MonoidalCategory.tensorRight (Δ[1] : SSet.{u}))
  have hle : a ≤ a.extend A' lt n t b w d :=
    { carrier_le := lt.le
      homotopy_restrict := by
        change a.homotopy.hom.h =
          (Subcomplex.homOfLE lt.le ▷ (Δ[1] : SSet.{u})) ≫
            (wI.desc a.homotopy.hom.h d.alpha d.boundary_alpha.symm)
        exact (wI.inl_desc _ _ _).symm }
  refine lt_of_le_of_ne hle ?_
  intro hEq
  have hc := congrArg Stage.carrier hEq
  exact lt.ne hc

private theorem Stage.carrier_eq_top_of_isMax {R : RepresentativeSystem p}
    [Fibration p] (a : Stage R) (ha : IsMax a) : a.carrier = ⊤ := by
  by_contra htop
  obtain ⟨A', lt, n, t, b, w⟩ :=
    boundary.exists_isPushout_of_ne_top a.carrier htop
  obtain ⟨d⟩ := exists_attachmentData a A' lt n t b w
  exact ha.not_lt (a.lt_extend A' lt n t b w d)

private theorem exists_topStage (R : RepresentativeSystem p) [Fibration p] :
    ∃ a : Stage R, a.carrier = ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximalStage R
  exact ⟨a, a.carrier_eq_top_of_isMax ha⟩

/-!
## The final minimal deformation retract

A maximal stage has carrier E. Its reversed homotopy gives a strong deformation retract onto the
core, fixed over B. Separation of the selected simplex classes gives minimality, and the
arrow-retract presentation gives horn lifting of the restricted map.
-/

private noncomputable def Stage.topIso {R : RepresentativeSystem p}
    (a : Stage R) (ha : a.carrier = ⊤) :
    (a.carrier : SSet.{u}) ≅ E :=
  Subcomplex.eqToIso ha ≪≫ Subcomplex.topIso E

private noncomputable def Stage.forwardHomotopyRelOver
    {R : RepresentativeSystem p} [Fibration p]
    (a : Stage R) (ha : a.carrier = ⊤) :
    HomotopyRelOver p
      ((a.topIso ha).inv ≫ a.retract ≫ R.core.ι)
      (𝟙 E) R.core := by
  let e := a.topIso ha
  have heHom : e.hom = a.carrier.ι := by
    change Subcomplex.homOfLE ha.le ≫ (Subcomplex.topIso E).hom =
      a.carrier.ι
    rw [Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hcoreInv : R.core.ι ≫ e.inv =
      Subcomplex.homOfLE a.core_le := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, heHom,
      Subcomplex.homOfLE_ι]
  let Hforward : E ⊗ Δ[1] ⟶ E :=
    (e.inv ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h
  have hzero : SSet.ι₀ ≫ Hforward =
      e.inv ≫ a.retract ≫ R.core.ι := by
    dsimp [Hforward]
    calc
      SSet.ι₀ ≫ ((e.inv ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h) =
        (SSet.ι₀ ≫ (e.inv ▷ (Δ[1] : SSet.{u}))) ≫
          a.homotopy.hom.h := (Category.assoc _ _ _).symm
      _ = (e.inv ≫ SSet.ι₀) ≫ a.homotopy.hom.h := by
        rw [SSet.ι₀_comp]
      _ = e.inv ≫ (SSet.ι₀ ≫ a.homotopy.hom.h) :=
        Category.assoc _ _ _
      _ = e.inv ≫ (a.retract ≫ R.core.ι) := by
        rw [a.homotopy.hom.h₀]
      _ = e.inv ≫ a.retract ≫ R.core.ι :=
        (Category.assoc _ _ _).symm
  have hone : SSet.ι₁ ≫ Hforward = 𝟙 E := by
    dsimp [Hforward]
    calc
      SSet.ι₁ ≫ ((e.inv ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h) =
        (SSet.ι₁ ≫ (e.inv ▷ (Δ[1] : SSet.{u}))) ≫
          a.homotopy.hom.h := (Category.assoc _ _ _).symm
      _ = (e.inv ≫ SSet.ι₁) ≫ a.homotopy.hom.h := by
        rw [SSet.ι₁_comp]
      _ = e.inv ≫ (SSet.ι₁ ≫ a.homotopy.hom.h) :=
        Category.assoc _ _ _
      _ = e.inv ≫ a.carrier.ι := by rw [a.homotopy.hom.h₁]
      _ = e.inv ≫ e.hom := by rw [heHom]
      _ = 𝟙 E := e.inv_hom_id
  have hstationary :
      (R.core.ι ▷ (Δ[1] : SSet.{u})) ≫ Hforward =
        fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          R.core.ι ≫ (e.inv ≫ a.retract ≫ R.core.ι) := by
    dsimp [Hforward]
    calc
      (R.core.ι ▷ (Δ[1] : SSet.{u})) ≫
          ((e.inv ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h) =
        ((R.core.ι ≫ e.inv) ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h := by
            rw [← Category.assoc, MonoidalCategory.comp_whiskerRight]
      _ = (Subcomplex.homOfLE a.core_le ▷ (Δ[1] : SSet.{u})) ≫
          a.homotopy.hom.h := by rw [hcoreInv]
      _ = fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.core.ι :=
        a.stationary
      _ = fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          (Subcomplex.homOfLE a.core_le ≫ a.retract) ≫ R.core.ι := by
        rw [a.retract_core, Category.id_comp]
      _ = fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          (R.core.ι ≫ e.inv) ≫ a.retract ≫ R.core.ι := by
        simp only [hcoreInv, Category.assoc]
      _ = fst (R.core : SSet.{u}) (Δ[1] : SSet.{u}) ≫
          R.core.ι ≫ (e.inv ≫ a.retract ≫ R.core.ι) := by
        simp only [Category.assoc]
  have hover : Hforward ≫ p =
      fst E (Δ[1] : SSet.{u}) ≫
        ((e.inv ≫ a.retract ≫ R.core.ι) ≫ p) := by
    dsimp [Hforward]
    calc
      ((e.inv ▷ (Δ[1] : SSet.{u})) ≫ a.homotopy.hom.h) ≫ p =
          (e.inv ▷ (Δ[1] : SSet.{u})) ≫
            (a.homotopy.hom.h ≫ p) := Category.assoc _ _ _
      _ = (e.inv ▷ (Δ[1] : SSet.{u})) ≫
          (fst (a.carrier : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            a.carrier.ι ≫ p) := by rw [a.homotopy.over]
      _ = fst E (Δ[1] : SSet.{u}) ≫ e.inv ≫ a.carrier.ι ≫ p := by
        simp only [CartesianMonoidalCategory.whiskerRight_fst_assoc]
      _ = fst E (Δ[1] : SSet.{u}) ≫ e.inv ≫
          ((a.retract ≫ R.core.ι) ≫ p) := by
        rw [a.homotopy.fac₀]
      _ = fst E (Δ[1] : SSet.{u}) ≫
          ((e.inv ≫ a.retract ≫ R.core.ι) ≫ p) := by
        simp only [Category.assoc]
  exact
    { toHomotopyRel :=
        { h := Hforward
          h₀ := hzero
          h₁ := hone
          stationary := by
            intro m z hz s
            have happ := ConcreteCategory.congr_hom
              (congr_app hstationary m) ⟨⟨z, hz⟩, s⟩
            exact happ }
      over := hover }

/-- Let p:E→B be a Kan fibration, R a separated representative system of fiberwise simplex homotopy,
and a deformation stage whose carrier is all E. Reverse its deformation from the retract
projection to identity to obtain a relative homotopy id_E→r≫ι fixed on the representative core
and lying over p. -/
private noncomputable def Stage.reverseHomotopyRelOver
    {R : RepresentativeSystem p} [Fibration p]
    (a : Stage R) (ha : a.carrier = ⊤) :
    HomotopyRelOver p (𝟙 E)
      ((a.topIso ha).inv ≫ a.retract ≫ R.core.ι) R.core :=
  (a.forwardHomotopyRelOver ha).symm

private noncomputable def Stage.strongDeformationRetract
    {R : RepresentativeSystem p} [Fibration p]
    (a : Stage R) (ha : a.carrier = ⊤) :
    StrongDeformationRetract R.core.ι := by
  let e := a.topIso ha
  let Hrev := a.reverseHomotopyRelOver ha
  have hretract : R.core.ι ≫ (e.inv ≫ a.retract) =
      𝟙 (R.core : SSet.{u}) := by
    have heHom : e.hom = a.carrier.ι := by
      change Subcomplex.homOfLE ha.le ≫ (Subcomplex.topIso E).hom =
        a.carrier.ι
      rw [Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
    have hcoreInv : R.core.ι ≫ e.inv =
        Subcomplex.homOfLE a.core_le := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, e.inv_hom_id, Category.comp_id, heHom,
        Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcoreInv, a.retract_core]
  exact
    { r := e.inv ≫ a.retract
      retract := hretract
      homotopy :=
        { h := Hrev.h
          h₀ := Hrev.h₀
          h₁ := by simpa only [e, Category.assoc] using Hrev.h₁
          stationary := by
            intro m z hz s
            apply Hrev.stationary
            simpa only [Subfunctor.range_ι] using hz } }

private def retractArrowOfSdrOver (M : E.Subcomplex)
    (sdr : StrongDeformationRetract M.ι)
    (hover : sdr.homotopy.h ≫ p =
      fst E (Δ[1] : SSet.{u}) ≫ p) :
    RetractArrow (M.ι ≫ p) p := by
  let H : SSet.FiberwiseHomotopy p p (𝟙 E) (sdr.r ≫ M.ι) :=
    { hom := sdr.homotopy.toHomotopy
      over := hover }
  exact
    { i := Arrow.homMk M.ι (𝟙 B) (by simp)
      r := Arrow.homMk sdr.r (𝟙 B) (by
        calc
          sdr.r ≫ (M.ι ≫ p) = (sdr.r ≫ M.ι) ≫ p :=
            (Category.assoc _ _ _).symm
          _ = p := H.fac₁
          _ = p ≫ 𝟙 B := (Category.comp_id _).symm)
      retract := by
        apply Arrow.hom_ext
        · exact sdr.retract
        · simp }

private theorem RepresentativeSystem.core_isMinimal
    (R : RepresentativeSystem p) : IsMinimal (R.core.ι ≫ p) := by
  intro n x y _hbase _hboundary hxy
  apply Subtype.ext
  apply R.separated
  · exact R.core_admissible n x.1 x.2
  · exact R.core_admissible n y.1 y.2
  · let f : Arrow.mk (R.core.ι ≫ p) ⟶ Arrow.mk p :=
      Arrow.homMk R.core.ι (𝟙 B) (by simp)
    simpa [f] using FiberwiseHomotopic.map hxy f

/-- Every Kan fibration p:E→B contains a subcomplex M such that M→B is a minimal Kan fibration and
M→E is a strong deformation retract stationary over B. -/
theorem nonempty_minimalSubfibration (p : E ⟶ B) [Fibration p] :
    Nonempty (MinimalSubfibration p) := by
  let R : RepresentativeSystem p := quotientRepresentativeSystem p
  obtain ⟨a, ha⟩ := exists_topStage R
  let sdr : StrongDeformationRetract R.core.ι :=
    a.strongDeformationRetract ha
  have hover : sdr.homotopy.h ≫ p =
      fst E (Δ[1] : SSet.{u}) ≫ p := by
    let Hrev := a.reverseHomotopyRelOver ha
    have hh : sdr.homotopy.h = Hrev.h := by
      dsimp [sdr, Stage.strongDeformationRetract, Hrev]
    have h := Hrev.over
    rw [hh]
    simpa only [HomotopyRelOver.h, Category.id_comp] using h
  let retractArrow : RetractArrow (R.core.ι ≫ p) p :=
    retractArrowOfSdrOver R.core sdr hover
  have hfibration : Fibration (R.core.ι ≫ p) := by
    rw [HomotopicalAlgebra.fibration_iff]
    exact (fibrations SSet.{u}).of_retract retractArrow
      (by rwa [← HomotopicalAlgebra.fibration_iff])
  exact ⟨{
    carrier := R.core
    sdr := sdr
    over := hover
    isMinimalFibration := ⟨hfibration, R.core_isMinimal⟩ }⟩

end MinimalFibration
end SSet
