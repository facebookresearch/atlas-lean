/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoSubdivisionSpan
public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoTripleSpanTarget
public import Mathlib.CategoryTheory.Equivalence

/-!
# Actual quotient-diagram extensions and their subdivision normalization

Weibel IV.7.3 defines morphisms between admissible exact rows by diagrams
whose middle quotient alone is identified up to isomorphism. The reverse
kernel mono and forward middle mono give the actual admissible-mono
subdivision factorization. Completed flags reconstruct all representatives.

This file constructs this category and its normalization equivalence. Its
target functor to Q and strict fibers are subsequent constructions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.ExactCategory Limits Opposite
open CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- An actual admissible exact row. Its category structure below uses
Weibel quotient diagrams, rather than ordinary short-complex morphisms. -/
structure ExtensionCategory where
  /-- The given row, including its given quotient object and map. -/
  row : ShortComplex C
  /-- Admissibility of the actual row. -/
  admissible : IsAdmissibleExact row

variable {C}

namespace ExtensionCategory

/-- The original admissible mono of a row, as an actual subdivision object. -/
def subdivisionObj (E : ExtensionCategory C) : AdmissibleMonoSubdivision (C := C) :=
  SegalSubdivision.mk (AdmissibleMonoCategory (C := C))
    (show (⟨E.row.X₁⟩ : AdmissibleMonoCategory (C := C)) ⟶ ⟨E.row.X₂⟩ from
      ⟨E.row.f, isAdmissibleMono_f E.admissible⟩)

/-- The normalized object retains the given row's mono exactly. -/
@[simp]
theorem subdivisionObj_val (E : ExtensionCategory C) :
    (subdivisionObj E).val.hom = E.row.f := rfl

end ExtensionCategory

/-- An actual Weibel quotient diagram from `E'` to `E`. Both `alpha` and
`beta` are admissible monos; only the middle quotient `D` varies in its relation. -/
structure ExtensionDiagram (E' E : ExtensionCategory C) where
  /-- The reverse mono on kernel objects. -/
  alpha : E.row.X₁ ⟶ E'.row.X₁
  /-- Admissibility of the reverse kernel mono. -/
  alpha_admissible : IsAdmissibleMono alpha
  /-- The forward mono on middle objects. -/
  beta : E'.row.X₂ ⟶ E.row.X₂
  /-- Admissibility of the forward middle mono. -/
  beta_admissible : IsAdmissibleMono beta
  /-- The actual middle quotient object. -/
  D : C
  /-- The actual mono of the middle row. -/
  j : E.row.X₁ ⟶ E'.row.X₂
  /-- The actual quotient map of the middle row. -/
  q : E'.row.X₂ ⟶ D
  /-- The middle row is a complex. -/
  zero : j ≫ q = 0
  /-- Admissibility of the actual middle row. -/
  admissible : IsAdmissibleExact (ShortComplex.mk j q zero)
  /-- The left quotient leg into the source's given quotient. -/
  lambda : D ⟶ E'.row.X₃
  /-- Admissibility of the left quotient epi. -/
  lambda_admissible : IsAdmissibleEpi lambda
  /-- The right quotient leg into the target's given quotient. -/
  mu : D ⟶ E.row.X₃
  /-- Admissibility of the right quotient mono. -/
  mu_admissible : IsAdmissibleMono mu
  /-- The middle mono factors through the source mono. -/
  j_eq : j = alpha ≫ E'.row.f
  /-- The forward middle mono recovers the target mono. -/
  j_beta : j ≫ beta = E.row.f
  /-- The left quotient square uses the source's given quotient map. -/
  q_lambda : q ≫ lambda = E'.row.g
  /-- The right quotient square uses the target's given quotient map. -/
  q_mu : q ≫ mu = beta ≫ E.row.g

namespace ExtensionDiagram

variable {E' E : ExtensionCategory C}

/-- The actual reverse/forward factorization of a quotient diagram. -/
def normalize (d : ExtensionDiagram E' E) :
    E'.subdivisionObj ⟶ E.subdivisionObj :=
  SegalSubdivision.homMk (AdmissibleMonoCategory (C := C))
    (⟨d.alpha, d.alpha_admissible⟩ :
      (⟨E.row.X₁⟩ : AdmissibleMonoCategory (C := C)) ⟶ ⟨E'.row.X₁⟩)
    (⟨d.beta, d.beta_admissible⟩ :
      (⟨E'.row.X₂⟩ : AdmissibleMonoCategory (C := C)) ⟶ ⟨E.row.X₂⟩) (by
        apply InducedWideCategory.Hom.ext
        change d.alpha ≫ E'.row.f ≫ d.beta = E.row.f
        rw [← Category.assoc, ← d.j_eq, d.j_beta])

/-- Normalization retains the original reverse kernel mono. -/
@[simp]
theorem normalize_alpha (d : ExtensionDiagram E' E) :
    (d.normalize.hom.1.unop).hom = d.alpha := rfl

/-- Normalization retains the original forward middle mono. -/
@[simp]
theorem normalize_beta (d : ExtensionDiagram E' E) :
    d.normalize.hom.2.hom = d.beta := rfl

/-- Reconstruct every raw quotient diagram from its actual admissible-mono
factorization, using the completed triple flag for all three quotient rows. -/
def ofNormalization (w : E'.subdivisionObj ⟶ E.subdivisionObj) : ExtensionDiagram E' E := by
  let a := w.hom.1.unop
  let b := w.hom.2
  let hi := isAdmissibleMono_f E'.admissible
  let F := admissibleMonoTripleFlag a.hom a.property E'.row.f hi b.hom b.property
  let h12 : (1 : Fin 5) ≤ (2 : Fin 5) := by decide
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  let h34 : (3 : Fin 5) ≤ (4 : Fin 5) := by decide
  let h13 := h12.trans h23
  let h14 := h13.trans h34
  have hw : (a.hom ≫ E'.row.f) ≫ b.hom = E.row.f :=
    admissibleMonoSubdivisionHom_factorization w
  have hlong : F.chain.map (homOfLE h14) = (a.hom ≫ E'.row.f) ≫ b.hom :=
    admissibleMonoTripleFlag_map_one_four a.hom a.property E'.row.f hi b.hom b.property h14
  have h1 : F.chain.obj (1 : Fin 5) = E.row.X₁ := rfl
  have h4 : F.chain.obj (4 : Fin 5) = E.row.X₂ := rfl
  have hsource : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h23)) E'.row.g E'.row.zero) := by
    exact E'.admissible
  have htargetZero : F.chain.map (homOfLE h14) ≫ E.row.g = 0 := by
    rw [hlong, hw]
    exact E.row.zero
  have htarget : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE h14)) E.row.g htargetZero) := by
    let e : ShortComplex.mk (F.chain.map (homOfLE h14)) E.row.g htargetZero ≅ E.row :=
      ShortComplex.isoMk (eqToIso h1) (eqToIso h4) (Iso.refl _)
        (by
          change 𝟙 _ ≫ E.row.f = F.chain.map (homOfLE h14) ≫ 𝟙 _
          rw [Category.id_comp, Category.comp_id]
          exact (hlong.trans hw).symm)
        (by
          change 𝟙 _ ≫ E.row.g = E.row.g ≫ 𝟙 _
          simp)
    exact isAdmissibleExact_of_iso e.symm E.admissible
  let eSource := F.intervalIsoOfExact h23 E'.row.g E'.row.zero hsource
  let eTarget := F.intervalIsoOfExact h14 E.row.g htargetZero htarget
  let S := F.intervalQuillenSpan h12 h23 h34
  refine {
    alpha := a.hom
    alpha_admissible := a.property
    beta := b.hom
    beta_admissible := b.property
    D := F.intervalQuotient (1 : Fin 5) (3 : Fin 5) h13
    j := a.hom ≫ E'.row.f
    q := F.intervalπ (1 : Fin 5) (3 : Fin 5) h13
    zero := F.interval_comp_π (1 : Fin 5) (3 : Fin 5) h13
    admissible := F.interval_exact (1 : Fin 5) (3 : Fin 5) h13
    lambda := S.l ≫ eSource.hom
    lambda_admissible := admissibleEpi_comp.comp_mem _ _ S.wl
      (IsAdmissibleEpi.of_isIso eSource.hom)
    mu := S.r ≫ eTarget.hom
    mu_admissible := admissibleMono_comp.comp_mem _ _ S.wr
      (IsAdmissibleMono.of_isIso eTarget.hom)
    j_eq := rfl
    j_beta := hw
    q_lambda := ?_
    q_mu := ?_ }
  · change F.intervalπ (1 : Fin 5) (3 : Fin 5) h13 ≫
        (F.intervalMap h13 h23 h12 le_rfl ≫ eSource.hom) = E'.row.g
    rw [← Category.assoc, F.intervalπ_naturality]
    have hid : F.chain.map (homOfLE (le_rfl : (3 : Fin 5) ≤ 3)) = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
    rw [hid, Category.id_comp]
    exact F.intervalπ_intervalIsoOfExact_hom h23 E'.row.g E'.row.zero hsource
  · change F.intervalπ (1 : Fin 5) (3 : Fin 5) h13 ≫
        (F.intervalMap h13 h14 le_rfl h34 ≫ eTarget.hom) = b.hom ≫ E.row.g
    rw [← Category.assoc, F.intervalπ_naturality, Category.assoc]
    rw [F.intervalπ_intervalIsoOfExact_hom]
    rfl

/-- Representative reconstruction retains the exact reverse kernel mono. -/
@[simp]
theorem ofNormalization_alpha (w : E'.subdivisionObj ⟶ E.subdivisionObj) :
    (ofNormalization w).alpha = (w.hom.1.unop).hom := rfl

/-- Representative reconstruction retains the exact forward middle mono. -/
@[simp]
theorem ofNormalization_beta (w : E'.subdivisionObj ⟶ E.subdivisionObj) :
    (ofNormalization w).beta = w.hom.2.hom := rfl

/-- Reconstructing a representative recovers the original complete
subdivision morphism, including its two admissible components. -/
@[simp]
theorem normalize_ofNormalization (w : E'.subdivisionObj ⟶ E.subdivisionObj) :
    (ofNormalization w).normalize = w := by
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    rfl
  · apply InducedWideCategory.Hom.ext
    rfl

/-- The actual diagram relation changes only its middle quotient object
through a commuting isomorphism. All other vertices and both monos are fixed. -/
def Rel (d e : ExtensionDiagram E' E) : Prop :=
  d.alpha = e.alpha ∧ d.beta = e.beta ∧
    ∃ k : d.D ≅ e.D, d.q ≫ k.hom = e.q ∧
      k.hom ≫ e.lambda = d.lambda ∧ k.hom ≫ e.mu = d.mu

/-- Isomorphic middle quotient diagrams have the same actual factorization. -/
theorem normalize_eq_of_rel {d e : ExtensionDiagram E' E} (h : Rel d e) :
    d.normalize = e.normalize := by
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    exact h.1
  · apply InducedWideCategory.Hom.ext
    exact h.2.1

/-- Equal factorizations determine a commuting middle-quotient isomorphism
by the actual cokernel universal properties of the two middle rows. -/
theorem rel_of_components_eq {d e : ExtensionDiagram E' E}
    (ha : d.alpha = e.alpha) (hb : d.beta = e.beta) : Rel d e := by
  have hj : d.j = e.j := by rw [d.j_eq, e.j_eq, ha]
  have heZero : d.j ≫ e.q = 0 := by rw [hj]; exact e.zero
  have heExact : IsAdmissibleExact (ShortComplex.mk d.j e.q heZero) := by
    simpa only [hj] using e.admissible
  let hd := isColimit_cokernelCofork_of_isAdmissibleExact d.admissible
  let he := isColimit_cokernelCofork_of_isAdmissibleExact heExact
  let k := hd.coconePointUniqueUpToIso he
  have hk : d.q ≫ k.hom = e.q := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hd he WalkingParallelPair.one
  let _ : Epi d.q := (isAdmissibleEpi_g d.admissible).epi
  refine ⟨ha, hb, k, hk, ?_, ?_⟩
  · apply (cancel_epi d.q).1
    rw [← Category.assoc, hk, e.q_lambda, d.q_lambda]
  · apply (cancel_epi d.q).1
    rw [← Category.assoc, hk, e.q_mu, d.q_mu, hb]

/-- The explicit middle-isomorphism relation is exactly equality of the
actual admissible-mono subdivision factorizations. -/
theorem rel_iff_normalize_eq (d e : ExtensionDiagram E' E) :
    Rel d e ↔ d.normalize = e.normalize := by
  refine ⟨normalize_eq_of_rel, fun h => rel_of_components_eq ?_ ?_⟩
  · exact congrArg (fun f => (f.hom.1.unop).hom) h
  · exact congrArg (fun f => f.hom.2.hom) h

/-- The actual middle-quotient diagram relation is an equivalence relation. -/
def setoid (E' E : ExtensionCategory C) : Setoid (ExtensionDiagram E' E) where
  r := Rel
  iseqv := {
    refl := fun d => (rel_iff_normalize_eq d d).mpr rfl
    symm := fun {d e} h => (rel_iff_normalize_eq e d).mpr
      ((rel_iff_normalize_eq d e).mp h).symm
    trans := fun {d e f} h k => (rel_iff_normalize_eq d f).mpr
      (((rel_iff_normalize_eq d e).mp h).trans ((rel_iff_normalize_eq e f).mp k)) }

/-- The identity diagram uses the actual given row and its given quotient,
with identity maps at all four comparison vertices. -/
def id (E : ExtensionCategory C) : ExtensionDiagram E E where
  alpha := 𝟙 _
  alpha_admissible := IsAdmissibleMono.id _
  beta := 𝟙 _
  beta_admissible := IsAdmissibleMono.id _
  D := E.row.X₃
  j := E.row.f
  q := E.row.g
  zero := E.row.zero
  admissible := E.admissible
  lambda := 𝟙 _
  lambda_admissible := IsAdmissibleEpi.id _
  mu := 𝟙 _
  mu_admissible := IsAdmissibleMono.id _
  j_eq := by simp
  j_beta := by simp
  q_lambda := by simp
  q_mu := by simp

/-- The literal identity diagram is the actual identity factorization. -/
@[simp]
theorem normalize_id (E : ExtensionCategory C) : (id E).normalize = 𝟙 E.subdivisionObj := by
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    rfl
  · apply InducedWideCategory.Hom.ext
    rfl

end ExtensionDiagram

namespace ExtensionCategory

/-- Actual extension morphisms are the quotient by the commuting middle-D
isomorphism relation, in the natural universe `max u v`. -/
abbrev Hom (E' E : ExtensionCategory C) :=
  Quotient (ExtensionDiagram.setoid E' E)

/-- The full hom-set normalization, with constructive inverse representative
recovery; no quotient category or comparison witness is assumed. -/
def homNormalization {E' E : ExtensionCategory C} :
    Hom E' E ≃ (E'.subdivisionObj ⟶ E.subdivisionObj) where
  toFun := Quotient.lift ExtensionDiagram.normalize
    (fun _ _ h => ExtensionDiagram.normalize_eq_of_rel h)
  invFun w := Quotient.mk _ (ExtensionDiagram.ofNormalization w)
  left_inv f := by
    refine Quotient.inductionOn f ?_
    intro d
    apply Quotient.sound
    exact (ExtensionDiagram.rel_iff_normalize_eq _ _).mpr
      (ExtensionDiagram.normalize_ofNormalization d.normalize)
  right_inv := ExtensionDiagram.normalize_ofNormalization

/-- The hom equivalence preserves every original raw factorization. -/
@[simp]
theorem homNormalization_quotientMk {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    homNormalization (Quotient.mk (ExtensionDiagram.setoid E' E) d) = d.normalize := rfl

/-- The inverse hom comparison is the constructed complete raw representative. -/
@[simp]
theorem homNormalization_symm_apply {E' E : ExtensionCategory C}
    (w : E'.subdivisionObj ⟶ E.subdivisionObj) :
    homNormalization.symm w = Quotient.mk _ (ExtensionDiagram.ofNormalization w) := rfl

/-- The actual quotient-diagram category. Composition is transported through
the proven hom-set correspondence with the actual subdivision category. -/
instance category : Category.{max u v} (ExtensionCategory C) where
  Hom := Hom
  id E := Quotient.mk _ (ExtensionDiagram.id E)
  comp f g := homNormalization.symm (homNormalization f ≫ homNormalization g)
  id_comp := by
    intro E F f
    apply homNormalization.injective
    simp only [Equiv.apply_symm_apply, homNormalization_quotientMk, ExtensionDiagram.normalize_id,
      Category.id_comp]
  comp_id := by
    intro E F f
    apply homNormalization.injective
    simp only [Equiv.apply_symm_apply, homNormalization_quotientMk, ExtensionDiagram.normalize_id,
      Category.comp_id]
  assoc := by
    intro E F G H f g h
    apply homNormalization.injective
    simp only [Equiv.apply_symm_apply, Category.assoc]

/-- The actual category morphism represented by one complete raw diagram. -/
def mkHom {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) : E' ⟶ E :=
  Quotient.mk _ d

/-- Equality of category morphisms is exactly the middle-D diagram relation. -/
theorem mkHom_eq_iff {E' E : ExtensionCategory C} (d e : ExtensionDiagram E' E) :
    mkHom d = mkHom e ↔ ExtensionDiagram.Rel d e := Quotient.eq

/-- Normalization of a representative is its actual two-factor diagram. -/
@[simp]
theorem homNormalization_mkHom {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    homNormalization (mkHom d) = d.normalize := rfl

/-- Normalization preserves the actual category identity. -/
@[simp]
theorem homNormalization_id (E : ExtensionCategory C) :
    homNormalization (𝟙 E) = 𝟙 E.subdivisionObj := ExtensionDiagram.normalize_id E

/-- Normalization preserves every actual quotient-diagram composite. -/
@[simp]
theorem homNormalization_comp {E F G : ExtensionCategory C} (f : E ⟶ F) (g : F ⟶ G) :
    homNormalization (f ≫ g) = homNormalization f ≫ homNormalization g :=
  homNormalization.apply_symm_apply _

/-- A representative of the actual composite of two quotient-diagram classes. -/
theorem mkHom_comp {E F G : ExtensionCategory C}
    (d : ExtensionDiagram E F) (e : ExtensionDiagram F G) :
    (mkHom d : E ⟶ F) ≫ (mkHom e : F ⟶ G) =
      (mkHom (ExtensionDiagram.ofNormalization (E' := E) (E := G)
        (d.normalize ≫ e.normalize)) : E ⟶ G) :=
  rfl

/-- Actual composition reverses the order of the kernel factors. -/
theorem comp_alpha {E F G : ExtensionCategory C}
    (d : ExtensionDiagram E F) (e : ExtensionDiagram F G) :
    (homNormalization (E' := E) (E := G)
      ((mkHom d : E ⟶ F) ≫ (mkHom e : F ⟶ G))).hom.1.unop.hom =
      e.alpha ≫ d.alpha := rfl

/-- Actual composition preserves the forward order of the middle factors. -/
theorem comp_beta {E F G : ExtensionCategory C}
    (d : ExtensionDiagram E F) (e : ExtensionDiagram F G) :
    (homNormalization (E' := E) (E := G)
      ((mkHom d : E ⟶ F) ≫ (mkHom e : F ⟶ G))).hom.2.hom =
      d.beta ≫ e.beta := rfl

/-- The actual row-to-subdivision normalization functor. -/
def normalization : ExtensionCategory C ⥤ AdmissibleMonoSubdivision (C := C) where
  obj := subdivisionObj
  map := homNormalization
  map_id := homNormalization_id
  map_comp := homNormalization_comp

/-- The normalization functor is fully faithful by the constructed full
hom-set comparison, not by a supplied equivalence. -/
def normalizationFullyFaithful : (normalization (C := C)).FullyFaithful where
  preimage := homNormalization.symm
  map_preimage := homNormalization.apply_symm_apply
  preimage_map := homNormalization.symm_apply_apply

/-- The selected exact completion of any actual subdivision mono. -/
def fromSubdivisionObj (x : AdmissibleMonoSubdivision (C := C)) : ExtensionCategory C where
  row := ShortComplex.mk x.val.hom
    (admissibleMonoQuotientπ x.val.hom x.val.property)
    (comp_admissibleMonoQuotientπ x.val.hom x.val.property)
  admissible := admissibleMonoQuotient_exact x.val.hom x.val.property

/-- Completing a subdivision mono and forgetting its quotient recovers the
same actual subdivision object. -/
@[simp]
theorem subdivisionObj_fromSubdivisionObj (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).subdivisionObj = x := by
  obtain ⟨A, B, f, rfl⟩ := SegalSubdivision.mk_surjective (AdmissibleMonoCategory (C := C)) x
  cases A
  cases B
  rcases f with ⟨g, hg⟩
  rfl

/-- The inverse object retains the original kernel object. -/
@[simp]
theorem fromSubdivisionObj_source (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).row.X₁ = (unop x.obj.1).obj := rfl

/-- The inverse object retains the original middle object. -/
@[simp]
theorem fromSubdivisionObj_middle (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).row.X₂ = x.obj.2.obj := rfl

/-- The inverse object uses the actual selected quotient completion. -/
@[simp]
theorem fromSubdivisionObj_quotient (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).row.X₃ = admissibleMonoQuotient x.val.hom x.val.property := rfl

/-- The inverse object retains the actual original admissible mono. -/
@[simp]
theorem fromSubdivisionObj_f (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).row.f = x.val.hom := rfl

/-- The inverse object's quotient map is the existing selected quotient map. -/
@[simp]
theorem fromSubdivisionObj_g (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).row.g = admissibleMonoQuotientπ x.val.hom x.val.property := rfl

/-- The selected quotient of the original mono is canonically isomorphic
to the row's given quotient, by the two actual cokernel universal properties. -/
def quotientIso (E : ExtensionCategory C) :
    admissibleMonoQuotient E.row.f (isAdmissibleMono_f E.admissible) ≅ E.row.X₃ :=
  (ofAdmissibleMono E.row.f (isAdmissibleMono_f E.admissible)).intervalIsoOfExact
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) E.row.g E.row.zero E.admissible

/-- The quotient comparison retains the row's original given quotient map. -/
@[reassoc (attr := simp)]
theorem quotientIso_projection (E : ExtensionCategory C) :
    admissibleMonoQuotientπ E.row.f (isAdmissibleMono_f E.admissible) ≫
        (quotientIso E).hom = E.row.g :=
  (ofAdmissibleMono E.row.f (isAdmissibleMono_f E.admissible)).intervalπ_intervalIsoOfExact_hom
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) E.row.g E.row.zero E.admissible

/-- The canonical object comparison from a selected completion back to the
same original subdivision object. -/
def normalizationCounitApp (x : AdmissibleMonoSubdivision (C := C)) :
    (fromSubdivisionObj x).subdivisionObj ≅ x :=
  eqToIso (subdivisionObj_fromSubdivisionObj x)

/-- The actual inverse normalization functor uses selected exact completions
on objects and the constructed raw representative on every morphism. -/
def denormalization : AdmissibleMonoSubdivision (C := C) ⥤ ExtensionCategory C where
  obj := fromSubdivisionObj
  map {x y} w := (homNormalization (E' := fromSubdivisionObj x) (E := fromSubdivisionObj y)).symm
    ((normalizationCounitApp x).hom ≫ w ≫ (normalizationCounitApp y).inv)
  map_id x := by
    apply homNormalization.injective
    rw [Equiv.apply_symm_apply, homNormalization_id, Category.id_comp, Iso.hom_inv_id]
  map_comp {x y z} f g := by
    apply homNormalization.injective
    rw [homNormalization_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The inverse functor's object is exactly the prescribed selected row. -/
@[simp]
theorem denormalization_obj (x : AdmissibleMonoSubdivision (C := C)) :
    denormalization.obj x = fromSubdivisionObj x := rfl

/-- Every inverse morphism is the actual representative reconstructed from
the given square with its canonical object comparisons. -/
theorem denormalization_map {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    denormalization.map w = mkHom (ExtensionDiagram.ofNormalization
      (E' := fromSubdivisionObj x) (E := fromSubdivisionObj y)
      ((normalizationCounitApp x).hom ≫ w ≫ (normalizationCounitApp y).inv)) := rfl

/-- Normalizing an inverse morphism gives the original square transported
through the two actual selected-row object comparisons. -/
theorem homNormalization_denormalization_map
    {x y : AdmissibleMonoSubdivision (C := C)} (w : x ⟶ y) :
    homNormalization (denormalization.map w) =
      (normalizationCounitApp x).hom ≫ w ≫ (normalizationCounitApp y).inv :=
  homNormalization.apply_symm_apply _

/-- The constructed counit of the actual normalization functor. -/
def normalizationCounitIso : denormalization (C := C) ⋙ normalization ≅ 𝟭 _ :=
  NatIso.ofComponents normalizationCounitApp (by
    intro x y w
    change homNormalization (denormalization.map w) ≫ (normalizationCounitApp y).hom =
      (normalizationCounitApp x).hom ≫ w
    rw [homNormalization_denormalization_map]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The chosen unit object comparison is the unique actual raw iso lifting
the inverse selected-row subdivision comparison. -/
def normalizationUnitApp (E : ExtensionCategory C) :
    E ≅ denormalization.obj (normalization.obj E) :=
  normalizationFullyFaithful.preimageIso (X := E)
    (Y := denormalization.obj (normalization.obj E))
    (normalizationCounitApp E.subdivisionObj).symm

/-- The unit retains the actual given kernel object. -/
theorem normalizationUnit_target_source (E : ExtensionCategory C) :
    (denormalization.obj (normalization.obj E)).row.X₁ = E.row.X₁ := rfl

/-- The unit retains the actual given middle object. -/
theorem normalizationUnit_target_middle (E : ExtensionCategory C) :
    (denormalization.obj (normalization.obj E)).row.X₂ = E.row.X₂ := rfl

/-- The unit target uses the prescribed selected quotient of the original mono. -/
theorem normalizationUnit_target_quotient (E : ExtensionCategory C) :
    (denormalization.obj (normalization.obj E)).row.X₃ =
      admissibleMonoQuotient E.row.f (isAdmissibleMono_f E.admissible) := rfl

/-- An explicit raw representative of the unit with the GIVEN quotient as
its middle D, rather than an assumed comparison or another endpoint. -/
def normalizationUnitDiagram (E : ExtensionCategory C) :
    ExtensionDiagram E (denormalization.obj (normalization.obj E)) where
  alpha := 𝟙 _
  alpha_admissible := IsAdmissibleMono.id _
  beta := 𝟙 _
  beta_admissible := IsAdmissibleMono.id _
  D := E.row.X₃
  j := E.row.f
  q := E.row.g
  zero := E.row.zero
  admissible := E.admissible
  lambda := 𝟙 _
  lambda_admissible := IsAdmissibleEpi.id _
  mu := (quotientIso E).inv
  mu_admissible := IsAdmissibleMono.of_isIso _
  j_eq := by
    change E.row.f = 𝟙 _ ≫ E.row.f
    simp
  j_beta := by
    change E.row.f ≫ 𝟙 _ = E.row.f
    simp
  q_lambda := by simp
  q_mu := by
    change E.row.g ≫ (quotientIso E).inv =
      𝟙 _ ≫ admissibleMonoQuotientπ E.row.f (isAdmissibleMono_f E.admissible)
    rw [← quotientIso_projection E, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

/-- The unit's forward raw map has the exact inverse counit factorization. -/
theorem homNormalization_unit_hom (E : ExtensionCategory C) :
    homNormalization (normalizationUnitApp E).hom =
      (normalizationCounitApp E.subdivisionObj).inv :=
  normalizationFullyFaithful.map_preimage _

/-- The unit's inverse raw map has the exact forward counit factorization. -/
theorem homNormalization_unit_inv (E : ExtensionCategory C) :
    homNormalization (normalizationUnitApp E).inv =
      (normalizationCounitApp E.subdivisionObj).hom :=
  normalizationFullyFaithful.map_preimage _

/-- The actual unit map is the class of the explicit given-quotient diagram. -/
theorem normalizationUnit_hom_mkHom (E : ExtensionCategory C) :
    (normalizationUnitApp E).hom = mkHom (normalizationUnitDiagram E) := by
  apply homNormalization.injective
  rw [homNormalization_unit_hom, homNormalization_mkHom]
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    rfl
  · apply InducedWideCategory.Hom.ext
    rfl

/-- The constructed unit of the actual normalization functor. -/
def normalizationUnitIso : 𝟭 (ExtensionCategory C) ≅ normalization ⋙ denormalization :=
  NatIso.ofComponents normalizationUnitApp (by
    intro E F f
    apply normalizationFullyFaithful.map_injective
    change homNormalization (f ≫ (normalizationUnitApp F).hom) =
      homNormalization ((normalizationUnitApp E).hom ≫ denormalization.map (normalization.map f))
    rw [homNormalization_comp, homNormalization_comp, homNormalization_unit_hom,
      homNormalization_unit_hom, homNormalization_denormalization_map]
    simp only [normalization, Iso.inv_hom_id_assoc])

/-- The complete constructed equivalence between actual Weibel quotient
diagrams and the admissible-mono Segal subdivision. -/
def normalizationEquivalence : ExtensionCategory C ≌ AdmissibleMonoSubdivision (C := C) where
  functor := normalization
  inverse := denormalization
  unitIso := normalizationUnitIso
  counitIso := normalizationCounitIso
  functor_unitIso_comp E := by
    change homNormalization (normalizationUnitApp E).hom ≫
      (normalizationCounitApp E.subdivisionObj).hom = 𝟙 _
    rw [homNormalization_unit_hom, Iso.inv_hom_id]

/-- The equivalence's inverse object is the actual selected exact completion. -/
@[simp]
theorem normalizationEquivalence_inverse_obj (x : AdmissibleMonoSubdivision (C := C)) :
    normalizationEquivalence.inverse.obj x = fromSubdivisionObj x := rfl

/-- The equivalence retains the constructed raw unit. -/
@[simp]
theorem normalizationEquivalence_unit_app (E : ExtensionCategory C) :
    normalizationEquivalence.unitIso.app E = normalizationUnitApp E := rfl

/-- The equivalence retains the constructed subdivision counit. -/
@[simp]
theorem normalizationEquivalence_counit_app (x : AdmissibleMonoSubdivision (C := C)) :
    normalizationEquivalence.counitIso.app x = normalizationCounitApp x := rfl

end ExtensionCategory

end AlgebraicKTheory

end
