/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Target
public import MathlibExt.KTheory.Exact.Quillen.Functor
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Actual exact-functor images of Weibel quotient-diagram extensions

The given admissible row and every map of its quotient diagram are sent
through the original exact functor. Its middle quotient is the image of
the original given middle quotient, not a selected replacement. Isomorphic
middle quotient diagrams remain related, and the target span is exactly
the existing Quillen span image. Source and target category worlds remain
independent. Functor composition and localized source comparisons are
subsequent obligations, with no such conclusion supplied as an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem extensionMapAdmissibleMono {X Y : C} {i : X ⟶ Y}
    (hi : IsAdmissibleMono i) : IsAdmissibleMono (F.map i) := by
  obtain ⟨Z, q, w, h⟩ := hi
  exact ⟨F.obj Z, F.map q, _, F.map_admissibleExact _ h⟩

private theorem extensionMapAdmissibleEpi {X Y : C} {q : X ⟶ Y}
    (hq : IsAdmissibleEpi q) : IsAdmissibleEpi (F.map q) := by
  obtain ⟨Z, i, w, h⟩ := hq
  exact ⟨F.obj Z, F.map i, _, F.map_admissibleExact _ h⟩

/-- The image retains the original given admissible row and its three object images. -/
public def ExtensionCategory.mapObject (E : ExtensionCategory C) : ExtensionCategory D where
  row := E.row.map F
  admissible := F.map_admissibleExact E.row E.admissible

private theorem mapObjectRowComputed (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F E).row = E.row.map F := rfl

/-- The exact given row is retained by the image construction. -/
public theorem ExtensionCategory.mapObject_row (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F E).row = E.row.map F :=
  mapObjectRowComputed F E

private theorem mapObjectWholeComputed (E : ExtensionCategory C) :
    ExtensionCategory.mapObject F E =
      (⟨E.row.map F, F.map_admissibleExact E.row E.admissible⟩ : ExtensionCategory D) := rfl

/-- The image is the complete original mapped row, including its actual admissibility proof. -/
public theorem ExtensionCategory.mapObject_eq_mk (E : ExtensionCategory C) :
    ExtensionCategory.mapObject F E =
      (⟨E.row.map F, F.map_admissibleExact E.row E.admissible⟩ : ExtensionCategory D) :=
  mapObjectWholeComputed F E

private theorem mapObjectComponentsComputed (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F E).row.X₁ = F.obj E.row.X₁ ∧
      (ExtensionCategory.mapObject F E).row.X₂ = F.obj E.row.X₂ ∧
      (ExtensionCategory.mapObject F E).row.X₃ = F.obj E.row.X₃ := ⟨rfl, rfl, rfl⟩

/-- The original kernel, middle and given quotient objects have their actual mapped views. -/
public theorem ExtensionCategory.mapObject_components (E : ExtensionCategory C) :
    (ExtensionCategory.mapObject F E).row.X₁ = F.obj E.row.X₁ ∧
      (ExtensionCategory.mapObject F E).row.X₂ = F.obj E.row.X₂ ∧
      (ExtensionCategory.mapObject F E).row.X₃ = F.obj E.row.X₃ :=
  mapObjectComponentsComputed F E

omit [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] [F.IsExact] in
private theorem extensionMappedRowZero
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    F.map d.j ≫ F.map d.q = 0 :=
  (F.map_comp d.j d.q).symm.trans
    ((congrArg F.map d.zero).trans (F.map_zero E.row.X₁ d.D))

/-- The original reverse/forward monos and every given middle quotient leg are mapped literally. -/
public def ExtensionDiagram.map
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    ExtensionDiagram (ExtensionCategory.mapObject F E') (ExtensionCategory.mapObject F E) where
  alpha := F.map d.alpha
  alpha_admissible := extensionMapAdmissibleMono F d.alpha_admissible
  beta := F.map d.beta
  beta_admissible := extensionMapAdmissibleMono F d.beta_admissible
  D := F.obj d.D
  j := F.map d.j
  q := F.map d.q
  zero := extensionMappedRowZero F d
  admissible := F.map_admissibleExact (ShortComplex.mk d.j d.q d.zero) d.admissible
  lambda := F.map d.lambda
  lambda_admissible := extensionMapAdmissibleEpi F d.lambda_admissible
  mu := F.map d.mu
  mu_admissible := extensionMapAdmissibleMono F d.mu_admissible
  j_eq := (congrArg F.map d.j_eq).trans (F.map_comp d.alpha E'.row.f)
  j_beta := (F.map_comp d.j d.beta).symm.trans (congrArg F.map d.j_beta)
  q_lambda := (F.map_comp d.q d.lambda).symm.trans (congrArg F.map d.q_lambda)
  q_mu := (F.map_comp d.q d.mu).symm.trans
    ((congrArg F.map d.q_mu).trans (F.map_comp d.beta E.row.g))

private theorem mapDiagramCharacteristicComputed
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    HEq (ExtensionDiagram.map F d).alpha (F.map d.alpha) ∧
      HEq (ExtensionDiagram.map F d).beta (F.map d.beta) ∧
      (ExtensionDiagram.map F d).D = F.obj d.D ∧
      HEq (ExtensionDiagram.map F d).j (F.map d.j) ∧
      HEq (ExtensionDiagram.map F d).q (F.map d.q) ∧
      HEq (ExtensionDiagram.map F d).lambda (F.map d.lambda) ∧
      HEq (ExtensionDiagram.map F d).mu (F.map d.mu) :=
  ⟨heq_of_eq rfl, heq_of_eq rfl, rfl, heq_of_eq rfl, heq_of_eq rfl,
    heq_of_eq rfl, heq_of_eq rfl⟩

/-- Every original quotient-diagram value is retained with its dependent endpoint views. -/
public theorem ExtensionDiagram.map_characteristic
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    HEq (ExtensionDiagram.map F d).alpha (F.map d.alpha) ∧
      HEq (ExtensionDiagram.map F d).beta (F.map d.beta) ∧
      (ExtensionDiagram.map F d).D = F.obj d.D ∧
      HEq (ExtensionDiagram.map F d).j (F.map d.j) ∧
      HEq (ExtensionDiagram.map F d).q (F.map d.q) ∧
      HEq (ExtensionDiagram.map F d).lambda (F.map d.lambda) ∧
      HEq (ExtensionDiagram.map F d).mu (F.map d.mu) :=
  mapDiagramCharacteristicComputed F d

private theorem mapDiagramRelComputed
    {E' E : ExtensionCategory C} {d e : ExtensionDiagram E' E}
    (h : ExtensionDiagram.Rel d e) :
    ExtensionDiagram.Rel (ExtensionDiagram.map F d) (ExtensionDiagram.map F e) := by
  rcases h with ⟨ha, hb, k, hq, hl, hm⟩
  let cd := ExtensionDiagram.map_characteristic F d
  let ce := ExtensionDiagram.map_characteristic F e
  let hd := cd.2.2.1
  let he := ce.2.2.1
  let l := eqToIso hd ≪≫ F.mapIso k ≪≫ (eqToIso he).symm
  have hAlpha : (ExtensionDiagram.map F d).alpha = (ExtensionDiagram.map F e).alpha :=
    eq_of_heq (cd.1.trans ((heq_of_eq (congrArg F.map ha)).trans ce.1.symm))
  have hBeta : (ExtensionDiagram.map F d).beta = (ExtensionDiagram.map F e).beta :=
    eq_of_heq (cd.2.1.trans ((heq_of_eq (congrArg F.map hb)).trans ce.2.1.symm))
  have hIso : HEq l.hom (F.map k.hom) :=
    (conj_eqToHom_iff_heq _ _ hd he).1 rfl
  refine ⟨hAlpha, hBeta, l, ?_, ?_, ?_⟩
  · have hCompose : HEq ((ExtensionDiagram.map F d).q ≫ l.hom)
        (F.map d.q ≫ F.map k.hom) :=
      heq_comp (ExtensionCategory.mapObject_components F E').2.1 hd he
        cd.2.2.2.2.1 hIso
    have hMapped : F.map d.q ≫ F.map k.hom = F.map e.q :=
      (F.map_comp d.q k.hom).symm.trans (congrArg F.map hq)
    exact eq_of_heq (hCompose.trans ((heq_of_eq hMapped).trans ce.2.2.2.2.1.symm))
  · have hCompose : HEq (l.hom ≫ (ExtensionDiagram.map F e).lambda)
        (F.map k.hom ≫ F.map e.lambda) :=
      heq_comp hd he (ExtensionCategory.mapObject_components F E').2.2
        hIso ce.2.2.2.2.2.1
    have hMapped : F.map k.hom ≫ F.map e.lambda = F.map d.lambda :=
      (F.map_comp k.hom e.lambda).symm.trans (congrArg F.map hl)
    exact eq_of_heq (hCompose.trans ((heq_of_eq hMapped).trans cd.2.2.2.2.2.1.symm))
  · have hCompose : HEq (l.hom ≫ (ExtensionDiagram.map F e).mu)
        (F.map k.hom ≫ F.map e.mu) :=
      heq_comp hd he (ExtensionCategory.mapObject_components F E).2.2
        hIso ce.2.2.2.2.2.2
    have hMapped : F.map k.hom ≫ F.map e.mu = F.map d.mu :=
      (F.map_comp k.hom e.mu).symm.trans (congrArg F.map hm)
    exact eq_of_heq (hCompose.trans ((heq_of_eq hMapped).trans cd.2.2.2.2.2.2.symm))

/-- The original middle-quotient relation is preserved with canonical image-object transports. -/
public theorem ExtensionDiagram.map_rel
    {E' E : ExtensionCategory C} {d e : ExtensionDiagram E' E}
    (h : ExtensionDiagram.Rel d e) :
    ExtensionDiagram.Rel (ExtensionDiagram.map F d) (ExtensionDiagram.map F e) :=
  mapDiagramRelComputed F h

private theorem mapDiagramSpanComputed
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    (ExtensionDiagram.map F d).toQuillenSpan = QuillenSpan.map F d.toQuillenSpan := rfl

/-- The whole given target span has the original Quillen span image and endpoint views. -/
public theorem ExtensionDiagram.map_toQuillenSpan_heq
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    HEq (ExtensionDiagram.map F d).toQuillenSpan (QuillenSpan.map F d.toQuillenSpan) :=
  heq_of_eq (mapDiagramSpanComputed F d)

private theorem mapTargetRepresentativeComputed
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    HEq (QuillenQ.mkHom
        (X := (⟨(ExtensionCategory.mapObject F E').row.X₃⟩ : QuillenQ D))
        (Y := (⟨(ExtensionCategory.mapObject F E).row.X₃⟩ : QuillenQ D))
        (ExtensionDiagram.map F d).toQuillenSpan)
      ((QuillenQ.map F).map (QuillenQ.mkHom
        (X := (⟨E'.row.X₃⟩ : QuillenQ C)) (Y := (⟨E.row.X₃⟩ : QuillenQ C))
        d.toQuillenSpan)) := by
  have hSpan := mapDiagramSpanComputed F d
  have hRaw := congrArg (fun s : QuillenSpan (F.obj E'.row.X₃) (F.obj E.row.X₃) =>
    QuillenQ.mkHom (X := (⟨F.obj E'.row.X₃⟩ : QuillenQ D))
      (Y := (⟨F.obj E.row.X₃⟩ : QuillenQ D)) s) hSpan
  exact (heq_of_eq hRaw).trans (heq_of_eq
    (QuillenQ.map_mk F (X := (⟨E'.row.X₃⟩ : QuillenQ C))
      (Y := (⟨E.row.X₃⟩ : QuillenQ C)) d.toQuillenSpan).symm)

/-- The actual mapped target representative, before its endpoint equality transports. -/
public theorem ExtensionDiagram.map_targetRepresentative_heq
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    HEq (QuillenQ.mkHom
        (X := (⟨(ExtensionCategory.mapObject F E').row.X₃⟩ : QuillenQ D))
        (Y := (⟨(ExtensionCategory.mapObject F E).row.X₃⟩ : QuillenQ D))
        (ExtensionDiagram.map F d).toQuillenSpan)
      ((QuillenQ.map F).map (QuillenQ.mkHom
        (X := (⟨E'.row.X₃⟩ : QuillenQ C)) (Y := (⟨E.row.X₃⟩ : QuillenQ C))
        d.toQuillenSpan)) :=
  mapTargetRepresentativeComputed F d

/-- Canonical quotient-object transports give the exact original Quillen target equation. -/
public theorem ExtensionDiagram.map_targetRepresentative
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    let hx := congrArg (fun X : D => (⟨X⟩ : QuillenQ D))
      (ExtensionCategory.mapObject_components F E').2.2
    let hy := congrArg (fun X : D => (⟨X⟩ : QuillenQ D))
      (ExtensionCategory.mapObject_components F E).2.2
    eqToHom hx.symm ≫ QuillenQ.mkHom
        (X := (⟨(ExtensionCategory.mapObject F E').row.X₃⟩ : QuillenQ D))
        (Y := (⟨(ExtensionCategory.mapObject F E).row.X₃⟩ : QuillenQ D))
        (ExtensionDiagram.map F d).toQuillenSpan ≫ eqToHom hy =
      (QuillenQ.map F).map (QuillenQ.mkHom
        (X := (⟨E'.row.X₃⟩ : QuillenQ C)) (Y := (⟨E.row.X₃⟩ : QuillenQ C))
        d.toQuillenSpan) := by
  exact ((conj_eqToHom_iff_heq' _ _ _ _).2
    (ExtensionDiagram.map_targetRepresentative_heq F d).symm).symm

/-- Map the original diagram class through the literal exact-functor image. -/
public def ExtensionCategory.mapHom {E' E : ExtensionCategory C} (a : E' ⟶ E) :
    ExtensionCategory.mapObject F E' ⟶ ExtensionCategory.mapObject F E :=
  Quotient.map (ExtensionDiagram.map F) (fun _ _ h => ExtensionDiagram.map_rel F h) a

private theorem extensionMapHomMkComputed
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    ExtensionCategory.mapHom F (ExtensionCategory.mkHom d) =
      ExtensionCategory.mkHom (ExtensionDiagram.map F d) := rfl

/-- The quotient map retains every original mapped representative. -/
public theorem ExtensionCategory.mapHom_mkHom
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    ExtensionCategory.mapHom F (ExtensionCategory.mkHom d) =
      ExtensionCategory.mkHom (ExtensionDiagram.map F d) :=
  extensionMapHomMkComputed F d

private theorem extensionMapHomIdComputed (E : ExtensionCategory C) :
    ExtensionCategory.mapHom F (𝟙 E) = 𝟙 (ExtensionCategory.mapObject F E) := by
  change ExtensionCategory.mkHom (ExtensionDiagram.map F (ExtensionDiagram.id E)) =
    ExtensionCategory.mkHom (ExtensionDiagram.id (ExtensionCategory.mapObject F E))
  apply (ExtensionCategory.mkHom_eq_iff _ _).2
  apply ExtensionDiagram.rel_of_components_eq
  · change F.map (𝟙 E.row.X₁) = 𝟙 (F.obj E.row.X₁)
    exact F.map_id E.row.X₁
  · change F.map (𝟙 E.row.X₂) = 𝟙 (F.obj E.row.X₂)
    exact F.map_id E.row.X₂

private theorem originalExtensionCompositeAlpha
    {A B E : ExtensionCategory C} (d : ExtensionDiagram A B) (e : ExtensionDiagram B E) :
    (ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)).alpha =
      e.alpha ≫ d.alpha := by
  let w := d.normalize ≫ e.normalize
  let u := ExtensionCategory.homNormalization
    (ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom e)
  have hNorm : u = w :=
    (ExtensionCategory.homNormalization_comp _ _).trans
      (congrArg₂ (fun a b => a ≫ b)
        (ExtensionCategory.homNormalization_mkHom d)
        (ExtensionCategory.homNormalization_mkHom e))
  have hProject := congrArg
    (fun k : A.subdivisionObj ⟶ E.subdivisionObj => k.hom.1.unop.hom) hNorm
  have hView := heq_of_eq (ExtensionDiagram.ofNormalization_alpha w)
  have hComposite := heq_of_eq (ExtensionCategory.comp_alpha d e)
  exact eq_of_heq (hView.trans ((heq_of_eq hProject).symm.trans hComposite))

private theorem originalExtensionCompositeBeta
    {A B E : ExtensionCategory C} (d : ExtensionDiagram A B) (e : ExtensionDiagram B E) :
    (ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)).beta =
      d.beta ≫ e.beta := by
  let w := d.normalize ≫ e.normalize
  let u := ExtensionCategory.homNormalization
    (ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom e)
  have hNorm : u = w :=
    (ExtensionCategory.homNormalization_comp _ _).trans
      (congrArg₂ (fun a b => a ≫ b)
        (ExtensionCategory.homNormalization_mkHom d)
        (ExtensionCategory.homNormalization_mkHom e))
  have hProject := congrArg
    (fun k : A.subdivisionObj ⟶ E.subdivisionObj => k.hom.2.hom) hNorm
  have hView := heq_of_eq (ExtensionDiagram.ofNormalization_beta w)
  have hComposite := heq_of_eq (ExtensionCategory.comp_beta d e)
  exact eq_of_heq (hView.trans ((heq_of_eq hProject).symm.trans hComposite))

private theorem mappedExtensionCompositeRel
    {A B E : ExtensionCategory C} (d : ExtensionDiagram A B) (e : ExtensionDiagram B E) :
    ExtensionDiagram.Rel
      (ExtensionDiagram.map F (ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)))
      (ExtensionDiagram.ofNormalization
        ((ExtensionDiagram.map F d).normalize ≫ (ExtensionDiagram.map F e).normalize)) := by
  let c := ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)
  let d' := ExtensionDiagram.map F d
  let e' := ExtensionDiagram.map F e
  let t := ExtensionDiagram.ofNormalization (d'.normalize ≫ e'.normalize)
  let cd := ExtensionDiagram.map_characteristic F d
  let ce := ExtensionDiagram.map_characteristic F e
  let cc := ExtensionDiagram.map_characteristic F c
  have hAlphaMapped : F.map c.alpha = F.map e.alpha ≫ F.map d.alpha :=
    (congrArg F.map (originalExtensionCompositeAlpha d e)).trans
      (F.map_comp e.alpha d.alpha)
  have hAlphaParts : HEq (e'.alpha ≫ d'.alpha) (F.map e.alpha ≫ F.map d.alpha) :=
    heq_comp (ExtensionCategory.mapObject_components F E).1
      (ExtensionCategory.mapObject_components F B).1
      (ExtensionCategory.mapObject_components F A).1 ce.1 cd.1
  have hAlphaTarget := originalExtensionCompositeAlpha d' e'
  have hAlpha : (ExtensionDiagram.map F c).alpha = t.alpha :=
    eq_of_heq (cc.1.trans ((heq_of_eq hAlphaMapped).trans
      (hAlphaParts.symm.trans (heq_of_eq hAlphaTarget).symm)))
  have hBetaMapped : F.map c.beta = F.map d.beta ≫ F.map e.beta :=
    (congrArg F.map (originalExtensionCompositeBeta d e)).trans
      (F.map_comp d.beta e.beta)
  have hBetaParts : HEq (d'.beta ≫ e'.beta) (F.map d.beta ≫ F.map e.beta) :=
    heq_comp (ExtensionCategory.mapObject_components F A).2.1
      (ExtensionCategory.mapObject_components F B).2.1
      (ExtensionCategory.mapObject_components F E).2.1 cd.2.1 ce.2.1
  have hBetaTarget := originalExtensionCompositeBeta d' e'
  have hBeta : (ExtensionDiagram.map F c).beta = t.beta :=
    eq_of_heq (cc.2.1.trans ((heq_of_eq hBetaMapped).trans
      (hBetaParts.symm.trans (heq_of_eq hBetaTarget).symm)))
  exact ExtensionDiagram.rel_of_components_eq hAlpha hBeta

private theorem extensionMapHomCompComputed
    {A B E : ExtensionCategory C} (a : A ⟶ B) (b : B ⟶ E) :
    ExtensionCategory.mapHom F (a ≫ b) =
      ExtensionCategory.mapHom F a ≫ ExtensionCategory.mapHom F b := by
  refine Quotient.inductionOn a ?_
  intro d
  refine Quotient.inductionOn b ?_
  intro e
  let c := ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)
  let d' := ExtensionDiagram.map F d
  let e' := ExtensionDiagram.map F e
  let t := ExtensionDiagram.ofNormalization (d'.normalize ≫ e'.normalize)
  have hSource :
      ExtensionCategory.mapHom F (ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom e) =
        ExtensionCategory.mkHom (ExtensionDiagram.map F c) :=
    (congrArg (fun k : A ⟶ E => ExtensionCategory.mapHom F k)
      (ExtensionCategory.mkHom_comp d e)).trans (extensionMapHomMkComputed F c)
  have hMiddle : ExtensionCategory.mkHom (ExtensionDiagram.map F c) =
      ExtensionCategory.mkHom t :=
    (ExtensionCategory.mkHom_eq_iff _ _).2 (mappedExtensionCompositeRel F d e)
  have hTarget : ExtensionCategory.mkHom t =
      ExtensionCategory.mapHom F (ExtensionCategory.mkHom d) ≫
        ExtensionCategory.mapHom F (ExtensionCategory.mkHom e) :=
    (ExtensionCategory.mkHom_comp d' e').symm.trans
      (congrArg₂ (fun a b => a ≫ b)
        (extensionMapHomMkComputed F d).symm (extensionMapHomMkComputed F e).symm)
  exact hSource.trans (hMiddle.trans hTarget)

/-- The actual image on all rows and all Weibel quotient-diagram classes. -/
public def ExtensionCategory.mapFunctor : ExtensionCategory C ⥤ ExtensionCategory D where
  obj E := ExtensionCategory.mapObject F E
  map a := ExtensionCategory.mapHom F a
  map_id E := extensionMapHomIdComputed F E
  map_comp a b := extensionMapHomCompComputed F a b

private theorem extensionTargetSquareComputed :
    ExtensionCategory.mapFunctor F ⋙ ExtensionCategory.target (C := D) =
      ExtensionCategory.target (C := C) ⋙ QuillenQ.map F := by
  have hObject (E : ExtensionCategory C) :
      (ExtensionCategory.mapFunctor F ⋙ ExtensionCategory.target (C := D)).obj E =
        (ExtensionCategory.target (C := C) ⋙ QuillenQ.map F).obj E := rfl
  refine Functor.hext hObject ?_
  intro E' E a
  refine Quotient.inductionOn a ?_
  intro d
  have hMap : (ExtensionCategory.target (C := D)).map
      (ExtensionCategory.mapHom F (ExtensionCategory.mkHom d)) =
      (ExtensionCategory.target (C := D)).map
        (ExtensionCategory.mkHom (ExtensionDiagram.map F d)) :=
    congrArg (fun k : ExtensionCategory.mapObject F E' ⟶ ExtensionCategory.mapObject F E =>
      (ExtensionCategory.target (C := D)).map k) (extensionMapHomMkComputed F d)
  have hTarget := ExtensionCategory.target_map_mkHom (ExtensionDiagram.map F d)
  have hRaw := ExtensionDiagram.map_targetRepresentative_heq F d
  have hOriginal := congrArg
    (fun k : (⟨E'.row.X₃⟩ : QuillenQ C) ⟶ ⟨E.row.X₃⟩ => (QuillenQ.map F).map k)
    (ExtensionCategory.target_map_mkHom d).symm
  exact (heq_of_eq hMap).trans
    ((heq_of_eq hTarget).trans (hRaw.trans (heq_of_eq hOriginal)))

/-- The original given-quotient target commutes with the actual exact-functor image on every
class. -/
public theorem ExtensionCategory.mapFunctor_target :
    ExtensionCategory.mapFunctor F ⋙ ExtensionCategory.target (C := D) =
      ExtensionCategory.target (C := C) ⋙ QuillenQ.map F :=
  extensionTargetSquareComputed F


/-- The actual normalized composite retains the reverse order of the original kernel legs. -/
public theorem ExtensionDiagram.ofNormalization_comp_alpha
    {A B E : ExtensionCategory C} (d : ExtensionDiagram A B) (e : ExtensionDiagram B E) :
    (ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)).alpha =
      e.alpha ≫ d.alpha :=
  originalExtensionCompositeAlpha d e

/-- The actual normalized composite retains the forward order of the original middle legs. -/
public theorem ExtensionDiagram.ofNormalization_comp_beta
    {A B E : ExtensionCategory C} (d : ExtensionDiagram A B) (e : ExtensionDiagram B E) :
    (ExtensionDiagram.ofNormalization (d.normalize ≫ e.normalize)).beta =
      d.beta ≫ e.beta :=
  originalExtensionCompositeBeta d e


private theorem originalExtensionFunctorObjComputed (E : ExtensionCategory C) :
    (ExtensionCategory.mapFunctor F).obj E = ExtensionCategory.mapObject F E := rfl

/-- The actual extension functor retains its original given-row object image. -/
public theorem ExtensionCategory.mapFunctor_obj (E : ExtensionCategory C) :
    (ExtensionCategory.mapFunctor F).obj E = ExtensionCategory.mapObject F E :=
  originalExtensionFunctorObjComputed F E

private theorem originalExtensionFunctorMapComputed
    {E' E : ExtensionCategory C} (a : E' ⟶ E) :
    HEq ((ExtensionCategory.mapFunctor F).map a) (ExtensionCategory.mapHom F a) :=
  heq_of_eq rfl

/-- The whole functor morphism has its original quotient-image value and endpoint views. -/
public theorem ExtensionCategory.mapFunctor_map_heq
    {E' E : ExtensionCategory C} (a : E' ⟶ E) :
    HEq ((ExtensionCategory.mapFunctor F).map a) (ExtensionCategory.mapHom F a) :=
  originalExtensionFunctorMapComputed F a


/-- Equal original row objects and arrow views transport the actual normalized middle map. -/
public theorem ExtensionCategory.homNormalization_middle_heq_of_objects_eq
    {A B A' B' : ExtensionCategory D} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) :
    HEq (ExtensionCategory.homNormalization a).hom.2.hom
      (ExtensionCategory.homNormalization b).hom.2.hom := by
  cases hA
  cases hB
  cases h
  exact HEq.rfl

private theorem originalMappedMiddleComputed
    {E E' : ExtensionCategory C} (f : E ⟶ E') :
    HEq (ExtensionCategory.homNormalization (ExtensionCategory.mapHom F f)).hom.2.hom
      (F.map (ExtensionCategory.homNormalization f).hom.2.hom) := by
  refine Quotient.inductionOn f ?_
  intro d
  let dm := ExtensionDiagram.map F d
  have hMapped :
      (ExtensionCategory.homNormalization
        (ExtensionCategory.mapHom F (ExtensionCategory.mkHom d))).hom.2.hom = dm.beta :=
    (congrArg (fun a : ExtensionCategory.mapObject F E ⟶ ExtensionCategory.mapObject F E' =>
      (ExtensionCategory.homNormalization a).hom.2.hom)
        (ExtensionCategory.mapHom_mkHom F d)).trans (by rfl)
  have hOriginal : (ExtensionCategory.homNormalization
      (ExtensionCategory.mkHom d)).hom.2.hom = d.beta := rfl
  exact (heq_of_eq hMapped).trans
    ((ExtensionDiagram.map_characteristic F d).2.1.trans
      (heq_of_eq (congrArg F.map hOriginal).symm))

/-- The actual extension functor maps every original middle arrow through F. -/
public theorem ExtensionCategory.mapHom_middle_heq
    {E E' : ExtensionCategory C} (f : E ⟶ E') :
    HEq (ExtensionCategory.homNormalization (ExtensionCategory.mapHom F f)).hom.2.hom
      (F.map (ExtensionCategory.homNormalization f).hom.2.hom) :=
  originalMappedMiddleComputed F f

/-- The actual extension functor's middle object retains the given image object. -/
public theorem ExtensionCategory.mapFunctor_middle_obj (E : ExtensionCategory C) :
    ((ExtensionCategory.mapFunctor F).obj E).row.X₂ = F.obj E.row.X₂ :=
  (congrArg (fun A : ExtensionCategory D => A.row.X₂)
    (ExtensionCategory.mapFunctor_obj F E)).trans
      (ExtensionCategory.mapObject_components F E).2.1

private theorem originalFunctorMiddleComputed
    {E E' : ExtensionCategory C} (f : E ⟶ E') :
    HEq (ExtensionCategory.homNormalization ((ExtensionCategory.mapFunctor F).map f)).hom.2.hom
      (F.map (ExtensionCategory.homNormalization f).hom.2.hom) :=
  (ExtensionCategory.homNormalization_middle_heq_of_objects_eq
    (ExtensionCategory.mapFunctor_obj F E) (ExtensionCategory.mapFunctor_obj F E')
    (ExtensionCategory.mapFunctor_map_heq F f)).trans
      (ExtensionCategory.mapHom_middle_heq F f)

/-- The whole given-quotient functor retains the actual middle-arrow image. -/
public theorem ExtensionCategory.mapFunctor_middle_heq
    {E E' : ExtensionCategory C} (f : E ⟶ E') :
    HEq (ExtensionCategory.homNormalization ((ExtensionCategory.mapFunctor F).map f)).hom.2.hom
      (F.map (ExtensionCategory.homNormalization f).hom.2.hom) :=
  originalFunctorMiddleComputed F f

end AlgebraicKTheory

end
