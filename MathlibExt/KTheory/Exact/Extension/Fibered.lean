/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Fiber
public import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# The original extension target is fibered

The carried source constructs actual incoming-span lifts and the unique
comparison between original given-X row maps with equal target class.
The actual fiber counit transports that comparison to arbitrary source rows;
its maps preserve the original kernel and middle and cast only the given
quotient endpoint.

Every original extension arrow is cartesian in the same-base-arrow sense.
Composition closure is then proved by applying this result to the actual
composite, using its derived HomLift. Together with the constructed incoming
lifts this proves `Functor.IsFibered` for the original target. The existing
fibered-category theorem then gives the strongly cartesian universal property.
No cartesian property, category equivalence, splitting, or homotopy result is
supplied as a new premise.

Source: Weibel IV.7.7 / Exercise IV.7.2. This is a categorical result; cartesian
sum action, localization and the homotopy fibration remain later obligations.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits

universe u v

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

namespace ExtensionCategory

/-- The actual middle component determines the whole quotient-diagram class. -/
theorem hom_ext_of_middle {E' E : ExtensionCategory C} (f g : E' ⟶ E)
    (hb : (homNormalization f).hom.2.hom = (homNormalization g).hom.2.hom) : f = g := by
  revert hb
  refine Quotient.inductionOn₂ f g ?_
  intro d e hb
  change d.beta = e.beta at hb
  have hi : Mono E'.row.f := (isAdmissibleMono_f E'.admissible).mono
  have hm : Mono d.beta := d.beta_admissible.mono
  have hd : (d.alpha ≫ E'.row.f) ≫ d.beta = E.row.f := by
    rw [← d.j_eq, d.j_beta]
  have he : (e.alpha ≫ E'.row.f) ≫ e.beta = E.row.f := by
    rw [← e.j_eq, e.j_beta]
  have he' : (e.alpha ≫ E'.row.f) ≫ d.beta = E.row.f :=
    (congrArg (fun b : E'.row.X₂ ⟶ E.row.X₂ => (e.alpha ≫ E'.row.f) ≫ b) hb).trans he
  apply (mkHom_eq_iff d e).2
  apply ExtensionDiagram.rel_of_components_eq _ hb
  apply (cancel_mono E'.row.f).mp
  apply (cancel_mono d.beta).mp
  exact hd.trans he'.symm

/-- Every original extension morphism is monic, by its actual middle mono. -/
theorem morphism_mono {E' E : ExtensionCategory C} (f : E' ⟶ E) : Mono f := by
  have hbeta : IsAdmissibleMono (homNormalization f).hom.2.hom :=
    (homNormalization f).hom.2.property
  have hf : Mono (homNormalization f).hom.2.hom := hbeta.mono
  constructor
  intro T g h w
  apply hom_ext_of_middle g h
  apply (cancel_mono (homNormalization f).hom.2.hom).mp
  have hw := congrArg (fun k : T ⟶ E => (homNormalization k).hom.2.hom) w
  rw [homNormalization_comp, homNormalization_comp] at hw
  exact hw

end ExtensionCategory

private theorem rightSquare_isPullback {E' E : ExtensionCategory C}
    (d : ExtensionDiagram E' E) : IsPullback d.q d.beta d.mu E.row.g := by
  let M : ShortComplex C := ShortComplex.mk d.j d.q d.zero
  let φ : M ⟶ E.row :=
    { τ₁ := 𝟙 E.row.X₁
      τ₂ := d.beta
      τ₃ := d.mu
      comm₁₂ := by
        change (𝟙 E.row.X₁) ≫ E.row.f = d.j ≫ d.beta
        rw [Category.id_comp, d.j_beta]
      comm₂₃ := d.q_mu.symm }
  have hφ : IsIso φ.τ₁ := by
    change IsIso (𝟙 E.row.X₁)
    infer_instance
  exact isPullback_g_of_isAdmissibleExact_of_isIso_left φ d.admissible E.admissible

private def kernelIsoOfMiddleIso {X : C} (F G : FixedTargetExtension C X)
    (b : F.B ≅ G.B) (hp : b.hom ≫ G.p = F.p) :
    {a : F.A ≅ G.A // a.hom ≫ G.i = F.i ≫ b.hom} := by
  let hF := isLimit_kernelFork_of_isAdmissibleExact F.admissible
  let hG := isLimit_kernelFork_of_isAdmissibleExact G.admissible
  have hiF : Mono F.i := (isAdmissibleMono_f F.admissible).mono
  have hiG : Mono G.i := (isAdmissibleMono_f G.admissible).mono
  have hpInv : b.inv ≫ F.p = G.p := by
    calc
      b.inv ≫ F.p = b.inv ≫ (b.hom ≫ G.p) := congrArg (b.inv ≫ ·) hp.symm
      _ = (b.inv ≫ b.hom) ≫ G.p := (Category.assoc _ _ _).symm
      _ = G.p := by rw [b.inv_hom_id, Category.id_comp]
  have wz : (F.i ≫ b.hom) ≫ G.p = 0 := by
    rw [Category.assoc, hp, F.zero]
  have wzInv : (G.i ≫ b.inv) ≫ F.p = 0 := by
    rw [Category.assoc, hpInv, G.zero]
  let a := hG.lift (KernelFork.ofι (F.i ≫ b.hom) wz)
  let aInv := hF.lift (KernelFork.ofι (G.i ≫ b.inv) wzInv)
  have ha : a ≫ G.i = F.i ≫ b.hom := hG.fac _ WalkingParallelPair.zero
  have haInv : aInv ≫ F.i = G.i ≫ b.inv := hF.fac _ WalkingParallelPair.zero
  have haa : a ≫ aInv = 𝟙 F.A := by
    apply (cancel_mono F.i).mp
    rw [Category.assoc, haInv, ← Category.assoc, ha,
      Category.assoc, b.hom_inv_id, Category.comp_id]
    exact (Category.id_comp F.i).symm
  have haaInv : aInv ≫ a = 𝟙 G.A := by
    apply (cancel_mono G.i).mp
    rw [Category.assoc, ha, ← Category.assoc, haInv,
      Category.assoc, b.inv_hom_id, Category.comp_id]
    exact (Category.id_comp G.i).symm
  exact ⟨{ hom := a, inv := aInv, hom_inv_id := haa, inv_hom_id := haaInv }, ha⟩

namespace FixedTargetExtension

/-- Maps from given-X rows with the same original Q target class have exactly
one given-X identity-fiber comparison. The apex and kernel isomorphisms are derived. -/
theorem exists_unique_target_comparison {X : C} (F G : FixedTargetExtension C X)
    (E : ExtensionCategory C) (f : F.toExtension ⟶ E) (g : G.toExtension ⟶ E)
    (ht : (ExtensionCategory.target (C := C)).map f =
      (ExtensionCategory.target (C := C)).map g) :
    ∃! χ : F ⟶ G, ((fiberInclusion X).map χ).val ≫ g = f := by
  revert ht
  refine Quotient.inductionOn₂ f g ?_
  intro d e ht
  let f : F.toExtension ⟶ E := ExtensionCategory.mkHom d
  let g : G.toExtension ⟶ E := ExtensionCategory.mkHom e
  let qd : (⟨X⟩ : QuillenQ C) ⟶ (⟨E.row.X₃⟩ : QuillenQ C) :=
    QuillenQ.mkHom (X := (⟨X⟩ : QuillenQ C))
      (Y := (⟨E.row.X₃⟩ : QuillenQ C)) d.toQuillenSpan
  let qe : (⟨X⟩ : QuillenQ C) ⟶ (⟨E.row.X₃⟩ : QuillenQ C) :=
    QuillenQ.mkHom (X := (⟨X⟩ : QuillenQ C))
      (Y := (⟨E.row.X₃⟩ : QuillenQ C)) e.toQuillenSpan
  let tf : (⟨X⟩ : QuillenQ C) ⟶ (⟨E.row.X₃⟩ : QuillenQ C) :=
    (ExtensionCategory.target (C := C)).map f
  let tg : (⟨X⟩ : QuillenQ C) ⟶ (⟨E.row.X₃⟩ : QuillenQ C) :=
    (ExtensionCategory.target (C := C)).map g
  have hd : qd = tf := (ExtensionCategory.target_map_mkHom d).symm
  have he : qe = tg := (ExtensionCategory.target_map_mkHom e).symm
  have hfg : tf = tg := ht
  have hspan : qd = qe := hd.trans (hfg.trans he.symm)
  obtain ⟨se⟩ := (QuillenQ.mkHom_eq_iff).mp hspan
  let a : d.D ≅ e.D := apexIsoOfSpanIso se
  have hLambda : a.hom ≫ e.lambda = d.lambda := se.hom.hom_l
  have hμ : a.hom ≫ e.mu = d.mu := se.hom.hom_r
  have hμInv : a.inv ≫ d.mu = e.mu := se.inv.hom_r
  let pd := rightSquare_isPullback d
  let pe := rightSquare_isPullback e
  let b : F.B ⟶ G.B := pe.lift (d.q ≫ a.hom) d.beta (by
    rw [Category.assoc, hμ, d.q_mu])
  let bInv : G.B ⟶ F.B := pd.lift (e.q ≫ a.inv) e.beta (by
    rw [Category.assoc, hμInv, e.q_mu])
  have hbq : b ≫ e.q = d.q ≫ a.hom := pe.lift_fst _ _ _
  have hbβ : b ≫ e.beta = d.beta := pe.lift_snd _ _ _
  have hbInvβ : bInv ≫ d.beta = e.beta := pd.lift_snd _ _ _
  have hmD : Mono d.beta := d.beta_admissible.mono
  have hmE : Mono e.beta := e.beta_admissible.mono
  have hbb : b ≫ bInv = 𝟙 F.B := by
    apply (cancel_mono d.beta).mp
    rw [Category.assoc, hbInvβ, hbβ, Category.id_comp]
  have hbbInv : bInv ≫ b = 𝟙 G.B := by
    apply (cancel_mono e.beta).mp
    rw [Category.assoc, hbβ, hbInvβ, Category.id_comp]
  let bIso : F.B ≅ G.B :=
    { hom := b, inv := bInv, hom_inv_id := hbb, inv_hom_id := hbbInv }
  have hp : bIso.hom ≫ G.p = F.p := by
    change b ≫ G.p = F.p
    calc
      b ≫ G.p = b ≫ (e.q ≫ e.lambda) := congrArg (b ≫ ·) e.q_lambda.symm
      _ = (b ≫ e.q) ≫ e.lambda := (Category.assoc _ _ _).symm
      _ = (d.q ≫ a.hom) ≫ e.lambda := congrArg (· ≫ e.lambda) hbq
      _ = d.q ≫ (a.hom ≫ e.lambda) := Category.assoc _ _ _
      _ = d.q ≫ d.lambda := congrArg (d.q ≫ ·) hLambda
      _ = F.p := d.q_lambda
  let k := kernelIsoOfMiddleIso F G bIso hp
  let χ : F ⟶ G :=
    { a := k.val
      b := bIso
      comm_i := k.property.symm
      comm_p := hp }
  let U : FixedTargetExtension C X ⥤ ExtensionCategory C :=
    fiberInclusion X ⋙ Functor.Fiber.fiberInclusion
  let kχ : F.toExtension ⟶ G.toExtension := U.map χ
  have hk : kχ = ((fiberInclusion X).map χ).val := rfl
  have hkβ : (ExtensionCategory.homNormalization kχ).hom.2.hom = b :=
    (congrArg (fun t : F.toExtension ⟶ G.toExtension =>
      (ExtensionCategory.homNormalization t).hom.2.hom) hk).trans (inclusion_map_beta χ)
  have hfβ : (ExtensionCategory.homNormalization f).hom.2.hom = d.beta := rfl
  have hgβ : (ExtensionCategory.homNormalization g).hom.2.hom = e.beta := rfl
  have hOriginal : kχ ≫ g = f := by
    apply ExtensionCategory.hom_ext_of_middle
    have hc := congrArg
      (fun t : F.toExtension.subdivisionObj ⟶ E.subdivisionObj => t.hom.2.hom)
      (ExtensionCategory.homNormalization_comp kχ g)
    exact hc.trans ((congrArg (· ≫ (ExtensionCategory.homNormalization g).hom.2.hom)
      hkβ).trans ((congrArg (b ≫ ·) hgβ).trans (hbβ.trans hfβ.symm)))
  have hχ : ((fiberInclusion X).map χ).val ≫ g = f :=
    (congrArg (fun t : F.toExtension ⟶ G.toExtension => t ≫ g) hk).symm.trans hOriginal
  have hg : Mono g := ExtensionCategory.morphism_mono g
  refine ⟨χ, hχ, ?_⟩
  intro χ' hχ'
  apply (homEquiv F G).injective
  apply Subtype.ext
  apply (cancel_mono g).mp
  exact hχ'.trans hχ.symm

end FixedTargetExtension

end AlgebraicKTheory


namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Every original representative span admits the actual backward row lift,
with its given quotient, pullback middle, and exact target-map formula. -/
theorem exists_quillenSpanBaseChange (E : ExtensionCategory C) {X' : C}
    (S : QuillenSpan X' E.row.X₃) :
    ∃ (E' : ExtensionCategory C) (hX : E'.row.X₃ = X')
      (d : ExtensionDiagram E' E) (hD : d.D = S.apex),
      IsPullback d.q d.beta d.mu E.row.g ∧
      d.lambda = eqToHom hD ≫ S.l ≫ eqToHom hX.symm ∧
      d.mu = eqToHom hD ≫ S.r ∧
      Nonempty (IsLimit (KernelFork.ofι E'.row.f E'.row.zero)) ∧
      (target (C := C)).map (mkHom d) =
        eqToHom (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C)) hX) ≫
          QuillenQ.mkHom (X := (⟨X'⟩ : QuillenQ C))
            (Y := (⟨E.row.X₃⟩ : QuillenQ C)) S := by
  let P : AdmissibleEpiKernelPresentation E.row.g :=
    { kernel := E.row.X₁
      ι := E.row.f
      zero := E.row.zero
      exact := E.admissible }
  let Q : P.BaseChange S.r := P.baseChange S.r
  let L : AdmissibleEpiKernelPresentation S.l :=
    (AdmissibleEpiKernelPresentation.nonempty S.wl).some
  let R := Q.kernelPresentation.compositeBaseChange L
  let K : AdmissibleEpiKernelPresentation (Q.fst ≫ S.l) :=
    Q.kernelPresentation.composite L
  let E' : ExtensionCategory C :=
    { row := ShortComplex.mk K.ι (Q.fst ≫ S.l) K.zero
      admissible := K.exact }
  let d : ExtensionDiagram E' E :=
    { alpha := R.kernelLift
      alpha_admissible := isAdmissibleMono_f R.kernelPresentation.exact
      beta := Q.snd
      beta_admissible := isAdmissibleMono_of_isPullback Q.square S.wr P.epi_admissible
      D := S.apex
      j := Q.kernelLift
      q := Q.fst
      zero := Q.kernelLift_fst
      admissible := Q.kernelPresentation.exact
      lambda := S.l
      lambda_admissible := S.wl
      mu := S.r
      mu_admissible := S.wr
      j_eq := R.kernelLift_snd.symm
      j_beta := Q.kernelLift_snd
      q_lambda := rfl
      q_mu := Q.square.w }
  refine ⟨E', rfl, d, rfl, Q.square, ?_, ?_, ?_, ?_⟩
  · change S.l = (𝟙 S.apex) ≫ S.l ≫ (𝟙 X')
    simp only [Category.id_comp, Category.comp_id]
  · change S.r = (𝟙 S.apex) ≫ S.r
    exact (Category.id_comp S.r).symm
  · exact ⟨isLimit_kernelFork_of_isAdmissibleExact E'.admissible⟩
  · have hspan : d.toQuillenSpan = S := by
      cases S
      rfl
    let q : (⟨X'⟩ : QuillenQ C) ⟶ (⟨E.row.X₃⟩ : QuillenQ C) :=
      QuillenQ.mkHom (X := (⟨X'⟩ : QuillenQ C))
        (Y := (⟨E.row.X₃⟩ : QuillenQ C)) S
    have ht : (target (C := C)).map (mkHom d) = q :=
      (target_map_mkHom d).trans (congrArg
        (fun T : QuillenSpan X' E.row.X₃ =>
          QuillenQ.mkHom (X := (⟨X'⟩ : QuillenQ C))
            (Y := (⟨E.row.X₃⟩ : QuillenQ C)) T) hspan)
    change (target (C := C)).map (mkHom d) = (𝟙 (⟨X'⟩ : QuillenQ C)) ≫ q
    have hid : q = (𝟙 (⟨X'⟩ : QuillenQ C)) ≫ q := by
      exact (@Category.id_comp (QuillenQ C)
        (inferInstance : Category.{max u v} (QuillenQ C))
        (⟨X'⟩ : QuillenQ C) (⟨E.row.X₃⟩ : QuillenQ C) q).symm
    exact ht.trans hid

/-- An arbitrary incoming arrow of the actual Q category has a backward
extension-row lift; its target equality uses the derived quotient cast. -/
theorem exists_quillenArrowBaseChange (E : ExtensionCategory C) (X' : C)
    (f : (⟨X'⟩ : QuillenQ C) ⟶ (target (C := C)).obj E) :
    ∃ (E' : ExtensionCategory C)
      (h : (target (C := C)).obj E' = (⟨X'⟩ : QuillenQ C))
      (d : ExtensionDiagram E' E),
      IsPullback d.q d.beta d.mu E.row.g ∧
      (target (C := C)).map (mkHom d) = eqToHom h ≫ f := by
  refine Quotient.inductionOn f ?_
  intro S
  obtain ⟨E', hX, d, hD, hp, hLambda, hμ, hk, ht⟩ := exists_quillenSpanBaseChange E S
  exact ⟨E', congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C)) hX, d, hp, ht⟩

end AlgebraicKTheory.ExtensionCategory


namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem target_homLift_heq {A B : ExtensionCategory C} {R S : QuillenQ C}
    (f : R ⟶ S) (φ : A ⟶ B) (h : Functor.IsHomLift (target (C := C)) f φ) :
    HEq ((target (C := C)).map φ) f := by
  cases h
  rfl

/-- Every original extension arrow has the same-base-arrow cartesian property.
The identity-fiber factor is constructed from the actual fiber counit. -/
theorem target_isCartesian {R S : QuillenQ C} (f : R ⟶ S)
    {A B : ExtensionCategory C} (φ : A ⟶ B)
    [Functor.IsHomLift (target (C := C)) f φ] :
    Functor.IsCartesian (target (C := C)) f φ := by
  rcases R with ⟨X⟩
  refine { toIsHomLift := inferInstance, universal_property := ?_ }
  intro A' φ' hφ'
  let s : Functor.Fiber (target (C := C)) (⟨X⟩ : QuillenQ C) :=
    ⟨A, IsHomLift.domain_eq (target (C := C)) f φ⟩
  let t : Functor.Fiber (target (C := C)) (⟨X⟩ : QuillenQ C) :=
    ⟨A', IsHomLift.domain_eq (target (C := C)) f φ'⟩
  let F := (FixedTargetExtension.fromFiber (C := C) X).obj s
  let G := (FixedTargetExtension.fromFiber (C := C) X).obj t
  let cs : (FixedTargetExtension.fiberInclusion X).obj F ≅ s :=
    (FixedTargetExtension.fiberCounit X).app s
  let ct : (FixedTargetExtension.fiberInclusion X).obj G ≅ t :=
    (FixedTargetExtension.fiberCounit X).app t
  let φs : F.toExtension ⟶ B := cs.hom.val ≫ φ
  let φt : G.toExtension ⟶ B := ct.hom.val ≫ φ'
  have hcs : Functor.IsHomLift (target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      cs.hom.val := cs.hom.property
  have hct : Functor.IsHomLift (target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C))
      ct.hom.val := ct.hom.property
  have hs : Functor.IsHomLift (target (C := C)) f φs := by
    change Functor.IsHomLift (target (C := C)) f (cs.hom.val ≫ φ)
    simpa only [Category.id_comp] using
      (inferInstance : Functor.IsHomLift (target (C := C))
        ((𝟙 (⟨X⟩ : QuillenQ C)) ≫ f) (cs.hom.val ≫ φ))
  have ht : Functor.IsHomLift (target (C := C)) f φt := by
    change Functor.IsHomLift (target (C := C)) f (ct.hom.val ≫ φ')
    simpa only [Category.id_comp] using
      (inferInstance : Functor.IsHomLift (target (C := C))
        ((𝟙 (⟨X⟩ : QuillenQ C)) ≫ f) (ct.hom.val ≫ φ'))
  have hsEq : HEq ((target (C := C)).map φs) f :=
    target_homLift_heq (A := F.toExtension) (B := B)
      (R := (⟨X⟩ : QuillenQ C)) (S := S) f φs hs
  have htEq : HEq ((target (C := C)).map φt) f :=
    target_homLift_heq (A := G.toExtension) (B := B)
      (R := (⟨X⟩ : QuillenQ C)) (S := S) f φt ht
  have hmap : (target (C := C)).map φt = (target (C := C)).map φs :=
    eq_of_heq (htEq.trans hsEq.symm)
  obtain ⟨τ, hτ, _⟩ := FixedTargetExtension.exists_unique_target_comparison
    G F B φt φs hmap
  let χF : t ⟶ s :=
    ct.inv ≫ (FixedTargetExtension.fiberInclusion X).map τ ≫ cs.hom
  let χ : A' ⟶ A := χF.val
  have hχ : Functor.IsHomLift (target (C := C)) (𝟙 (⟨X⟩ : QuillenQ C)) χ :=
    χF.property
  have hfac : χ ≫ φ = φ' := by
    calc
      χ ≫ φ = ct.inv.val ≫
          (((FixedTargetExtension.fiberInclusion X).map τ).val ≫ φs) := by
        change ((ct.inv.val ≫ ((FixedTargetExtension.fiberInclusion X).map τ).val ≫
          cs.hom.val) ≫ φ) = ct.inv.val ≫
            (((FixedTargetExtension.fiberInclusion X).map τ).val ≫ (cs.hom.val ≫ φ))
        exact (Category.assoc ct.inv.val
          (((FixedTargetExtension.fiberInclusion X).map τ).val ≫ cs.hom.val) φ).trans
          (congrArg (ct.inv.val ≫ ·) (Category.assoc
            ((FixedTargetExtension.fiberInclusion X).map τ).val cs.hom.val φ))
      _ = ct.inv.val ≫ φt := congrArg (ct.inv.val ≫ ·) hτ
      _ = (ct.inv.val ≫ ct.hom.val) ≫ φ' := by
        change ct.inv.val ≫ (ct.hom.val ≫ φ') = _
        exact (Category.assoc _ _ _).symm
      _ = φ' := by
        have hi : ct.inv.val ≫ ct.hom.val = 𝟙 A' :=
          congrArg (fun k : t ⟶ t => k.val) ct.inv_hom_id
        rw [hi, Category.id_comp]
  have hmono : Mono φ := morphism_mono φ
  refine ⟨χ, ⟨hχ, hfac⟩, ?_⟩
  intro ψ hψ
  apply (cancel_mono φ).mp
  exact hψ.2.trans hfac.symm

/-- Every incoming Q arrow has an actual cartesian extension lift. -/
theorem target_isPreFibered : Functor.IsPreFibered (target (C := C)) := by
  constructor
  intro A R f
  rcases R with ⟨X⟩
  obtain ⟨A', hA', d, hp, hd⟩ := exists_quillenArrowBaseChange A X f
  have hl : Functor.IsHomLift (target (C := C)) f (mkHom d) := by
    apply IsHomLift.of_fac' (target (C := C)) f (mkHom d) hA' rfl
    simpa only [eqToHom_refl, Category.comp_id] using hd
  exact ⟨A', mkHom d, target_isCartesian f (mkHom d)⟩

/-- The original extension target is fibered, with composition closure proved
on every actual composite, not assumed from existence of weak cartesian lifts. -/
theorem target_isFibered : Functor.IsFibered (target (C := C)) where
  toIsPreFibered := target_isPreFibered
  comp {R S T} f g {A B D} φ ψ _ _ := by
    exact target_isCartesian (f ≫ g) (φ ≫ ψ)

/-- The strongly cartesian factorization property follows from the proved
fibered target and the original arrow's derived cartesian property. -/
theorem target_isStronglyCartesian {R S : QuillenQ C} (f : R ⟶ S)
    {A B : ExtensionCategory C} (φ : A ⟶ B)
    [Functor.IsHomLift (target (C := C)) f φ] :
    Functor.IsStronglyCartesian (target (C := C)) f φ := by
  have hf : Functor.IsFibered (target (C := C)) := target_isFibered
  have hφ : Functor.IsCartesian (target (C := C)) f φ := target_isCartesian f φ
  infer_instance

end AlgebraicKTheory.ExtensionCategory

end
