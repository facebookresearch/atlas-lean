/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesComplex
public import MathlibExt.Algebra.Homology.ChainComplex.HomCochainComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public meta import Mathlib.Tactic.DSimpPercent
public meta import Lean.Elab.Tactic.Omega

/-!
# Hom sequences of cycles and outgoing images

Precomposition reverses the cycles-term-image sequence of a chain complex
to a full-product Hom sequence. The target cochain complex retains its
differential. Projective outgoing images give degreewise Hom splittings.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace ChainComplex

universe u v
variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- The two-variable Hom map is zero when its source map is zero. -/
theorem homCochainComplexMap_zero_left {P P' : ChainComplex C ℤ}
    {Q Q' : CochainComplex C ℤ} (g : Q ⟶ Q') :
    homCochainComplexMap (0 : P' ⟶ P) g = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  have h := homCochainComplexMap_v (0 : P' ⟶ P) g n p q hpq z
  have hf : ((cochainComplexEquivalence C).functor.map (0 : P' ⟶ P)).f p = 0 := rfl
  change (((homCochainComplexMap (0 : P' ⟶ P) g).f n).hom z).v p q hpq = 0
  simpa only [hf, CategoryTheory.Limits.zero_comp] using h

end Preadditive

section Abelian

variable [Abelian C]

/-- Reverse the canonical source sequence by full-product Hom into the given target. -/
def homCyclesSequence (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{v} ℤ) :=
  let f : cyclesZeroComplex P ⟶ P :=
    (cyclesComplexInclusion (C := C) (c := ComplexShape.down ℤ)).app P
  let g : P ⟶ outgoingImageZeroComplex P :=
    (cyclesComplexProjection (C := C) (c := ComplexShape.down ℤ)).app P
  ShortComplex.mk (homCochainComplexMap g (𝟙 Q)) (homCochainComplexMap f (𝟙 Q)) (by
    have hfg : f ≫ g = 0 := (cyclesComplexSequence P).zero
    have h := homCochainComplexMap_comp g f (𝟙 Q) (𝟙 Q)
    simpa only [hfg, Category.id_comp, homCochainComplexMap_zero_left] using h)

/-- Its first object is Hom from the zero-differential outgoing images. -/
theorem homCyclesSequence_X₁ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) :
    (homCyclesSequence P Q).X₁ = homCochainComplex (outgoingImageZeroComplex P) Q := rfl

/-- Its middle object is the existing full total Hom of the complexes. -/
theorem homCyclesSequence_X₂ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) :
    (homCyclesSequence P Q).X₂ = homCochainComplex P Q := rfl

/-- Its third object is Hom from the zero-differential cycles. -/
theorem homCyclesSequence_X₃ (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) :
    (homCyclesSequence P Q).X₃ = homCochainComplex (cyclesZeroComplex P) Q := rfl

/-- The first arrow precomposes by the quotient onto the differential image. -/
theorem homCyclesSequence_f_v (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p q : ℤ) (hpq : p + n = q)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q n) :
    dsimp% only [cochainComplexEquivalence, ComplexShape.Embedding.restrictionFunctor, HomologicalComplex.restriction, outgoingImageZeroComplex, outgoingImageZeroComplexFunctor, cyclesZeroComplex, cyclesZeroComplexFunctor, Functor.pi'] (
    ((((homCyclesSequence P Q).f.f n).hom z).v p q hpq) =
      Abelian.factorThruImage (P.d (-p) ((ComplexShape.down ℤ).next (-p))) ≫
        z.v p q hpq) := by
  let qP : P ⟶ outgoingImageZeroComplex P :=
    (cyclesComplexProjection (C := C) (c := ComplexShape.down ℤ)).app P
  have hF : (homCyclesSequence P Q).f = homCochainComplexMap qP (𝟙 Q) := rfl
  have hPoint := congrArg (fun u : homCochainComplex (outgoingImageZeroComplex P) Q ⟶
      homCochainComplex P Q => (((u.f n).hom z).v p q hpq)) hF
  let A := (cochainComplexEquivalence C).functor.obj P
  let B := (cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)
  let α : A.X p ⟶ B.X p := ((cochainComplexEquivalence C).functor.map qP).f p
  let v : B.X p ⟶ Q.X q := z.v p q hpq
  have h := homCochainComplexMap_v qP (𝟙 Q) n p q hpq z
  have hα : α = Abelian.factorThruImage (P.d (-p) ((ComplexShape.down ℤ).next (-p))) := rfl
  have hId : (𝟙 Q : Q ⟶ Q).f q = 𝟙 (Q.X q) := rfl
  have hPost : α ≫ v ≫ (𝟙 Q : Q ⟶ Q).f q = α ≫ v :=
    (congrArg (fun t : Q.X q ⟶ Q.X q => α ≫ v ≫ t) hId).trans
      (congrArg (fun t : B.X p ⟶ Q.X q => α ≫ t) (Category.comp_id v))
  have hPre : α ≫ v = Abelian.factorThruImage (P.d (-p) ((ComplexShape.down ℤ).next (-p))) ≫ v :=
    congrArg (fun t : A.X p ⟶ B.X p => t ≫ v) hα
  exact hPoint.trans (h.trans (hPost.trans hPre))

/-- The second arrow precomposes by the cycles inclusion. -/
theorem homCyclesSequence_g_v (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (n p q : ℤ) (hpq : p + n = q)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence C).functor.obj P) Q n) :
    dsimp% only [cochainComplexEquivalence, ComplexShape.Embedding.restrictionFunctor, HomologicalComplex.restriction, outgoingImageZeroComplex, outgoingImageZeroComplexFunctor, cyclesZeroComplex, cyclesZeroComplexFunctor, Functor.pi'] (
    ((((homCyclesSequence P Q).g.f n).hom z).v p q hpq) =
      P.iCycles (-p) ≫ z.v p q hpq) := by
  let iP : cyclesZeroComplex P ⟶ P :=
    (cyclesComplexInclusion (C := C) (c := ComplexShape.down ℤ)).app P
  have hG : (homCyclesSequence P Q).g = homCochainComplexMap iP (𝟙 Q) := rfl
  have hPoint := congrArg (fun u : homCochainComplex P Q ⟶
      homCochainComplex (cyclesZeroComplex P) Q => (((u.f n).hom z).v p q hpq)) hG
  let A := (cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)
  let B := (cochainComplexEquivalence C).functor.obj P
  let α : A.X p ⟶ B.X p := ((cochainComplexEquivalence C).functor.map iP).f p
  let v : B.X p ⟶ Q.X q := z.v p q hpq
  have h := homCochainComplexMap_v iP (𝟙 Q) n p q hpq z
  have hα : α = P.iCycles (-p) := rfl
  have hId : (𝟙 Q : Q ⟶ Q).f q = 𝟙 (Q.X q) := rfl
  have hPost : α ≫ v ≫ (𝟙 Q : Q ⟶ Q).f q = α ≫ v :=
    (congrArg (fun t : Q.X q ⟶ Q.X q => α ≫ v ≫ t) hId).trans
      (congrArg (fun t : B.X p ⟶ Q.X q => α ≫ t) (Category.comp_id v))
  have hPre : α ≫ v = P.iCycles (-p) ≫ v :=
    congrArg (fun t : A.X p ⟶ B.X p => t ≫ v) hα
  exact hPoint.trans (h.trans (hPost.trans hPre))

/-- Pre/postcomposition maps form the simultaneous natural sequence map. -/
def homCyclesSequenceMap {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') : homCyclesSequence P Q ⟶ homCyclesSequence P' Q' := by
  let F := cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)
  let t : cyclesComplexSequence P' ⟶ cyclesComplexSequence P := F.map f
  refine
    { τ₁ := homCochainComplexMap t.τ₃ g
      τ₂ := homCochainComplexMap f g
      τ₃ := homCochainComplexMap t.τ₁ g
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · change homCochainComplexMap t.τ₃ g ≫
        homCochainComplexMap (cyclesComplexSequence P').g (𝟙 Q') =
      homCochainComplexMap (cyclesComplexSequence P).g (𝟙 Q) ≫ homCochainComplexMap f g
    have hLeft := homCochainComplexMap_comp t.τ₃ (cyclesComplexSequence P').g g (𝟙 Q')
    have hRight := homCochainComplexMap_comp (cyclesComplexSequence P).g f (𝟙 Q) g
    simp only [Category.comp_id, Category.id_comp] at hLeft hRight
    have h : (cyclesComplexSequence P').g ≫ t.τ₃ =
        f ≫ (cyclesComplexSequence P).g := t.comm₂₃.symm
    exact hLeft.trans ((congrArg
      (fun u : P' ⟶ outgoingImageZeroComplex P => homCochainComplexMap u g) h).trans hRight.symm)
  · change homCochainComplexMap f g ≫
        homCochainComplexMap (cyclesComplexSequence P').f (𝟙 Q') =
      homCochainComplexMap (cyclesComplexSequence P).f (𝟙 Q) ≫ homCochainComplexMap t.τ₁ g
    have hLeft := homCochainComplexMap_comp f (cyclesComplexSequence P').f g (𝟙 Q')
    have hRight := homCochainComplexMap_comp (cyclesComplexSequence P).f t.τ₁ (𝟙 Q) g
    simp only [Category.comp_id, Category.id_comp] at hLeft hRight
    have h : (cyclesComplexSequence P').f ≫ f =
        t.τ₁ ≫ (cyclesComplexSequence P).f := t.comm₁₂.symm
    exact hLeft.trans ((congrArg
      (fun u : cyclesZeroComplex P' ⟶ P => homCochainComplexMap u g) h).trans hRight.symm)

/-- Its middle component is precisely the two-variable Hom map. -/
theorem homCyclesSequenceMap_τ₂ {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    (homCyclesSequenceMap f g).τ₂ = homCochainComplexMap f g := rfl

/-- The left component uses the map between outgoing images. -/
theorem homCyclesSequenceMap_τ₁ {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    (homCyclesSequenceMap f g).τ₁ = homCochainComplexMap
      ((cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)).map f).τ₃ g := rfl

/-- The right component uses the cycles map of the source morphism. -/
theorem homCyclesSequenceMap_τ₃ {P P' : ChainComplex C ℤ} {Q Q' : CochainComplex C ℤ}
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    (homCyclesSequenceMap f g).τ₃ = homCochainComplexMap
      ((cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)).map f).τ₁ g := rfl

/-- Identities act as identities on the canonical full-Hom sequence. -/
theorem homCyclesSequenceMap_id (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ) :
    homCyclesSequenceMap (𝟙 P) (𝟙 Q) = 𝟙 (homCyclesSequence P Q) := by
  let F := cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)
  have hF : F.map (𝟙 P) = 𝟙 (F.obj P) := F.map_id P
  apply ShortComplex.Hom.ext
  · change homCochainComplexMap ((F.map (𝟙 P)).τ₃) (𝟙 Q) = 𝟙 _
    have h : (F.map (𝟙 P)).τ₃ = 𝟙 (outgoingImageZeroComplex P) :=
      congrArg (fun t : F.obj P ⟶ F.obj P => t.τ₃) hF
    exact (congrArg (fun u : outgoingImageZeroComplex P ⟶ outgoingImageZeroComplex P =>
      homCochainComplexMap u (𝟙 Q)) h).trans (homCochainComplexMap_id _ _)
  · exact homCochainComplexMap_id P Q
  · change homCochainComplexMap ((F.map (𝟙 P)).τ₁) (𝟙 Q) = 𝟙 _
    have h : (F.map (𝟙 P)).τ₁ = 𝟙 (cyclesZeroComplex P) :=
      congrArg (fun t : F.obj P ⟶ F.obj P => t.τ₁) hF
    exact (congrArg (fun u : cyclesZeroComplex P ⟶ cyclesZeroComplex P =>
      homCochainComplexMap u (𝟙 Q)) h).trans (homCochainComplexMap_id _ _)

/-- Composition preserves the contravariant source and covariant target order. -/
theorem homCyclesSequenceMap_comp {P P' P'' : ChainComplex C ℤ}
    {Q Q' Q'' : CochainComplex C ℤ}
    (f : P' ⟶ P) (f' : P'' ⟶ P') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    homCyclesSequenceMap f g ≫ homCyclesSequenceMap f' g' =
      homCyclesSequenceMap (f' ≫ f) (g ≫ g') := by
  let F := cyclesComplexSequenceFunctor (C := C) (c := ComplexShape.down ℤ)
  have hF : F.map (f' ≫ f) = F.map f' ≫ F.map f := F.map_comp f' f
  apply ShortComplex.Hom.ext
  · change homCochainComplexMap (F.map f).τ₃ g ≫ homCochainComplexMap (F.map f').τ₃ g' =
      homCochainComplexMap (F.map (f' ≫ f)).τ₃ (g ≫ g')
    rw [homCochainComplexMap_comp]
    have h : (F.map (f' ≫ f)).τ₃ = (F.map f').τ₃ ≫ (F.map f).τ₃ :=
      congrArg (fun t : F.obj P'' ⟶ F.obj P => t.τ₃) hF
    exact (congrArg (fun u : outgoingImageZeroComplex P'' ⟶ outgoingImageZeroComplex P =>
      homCochainComplexMap u (g ≫ g')) h).symm
  · exact homCochainComplexMap_comp f f' g g'
  · change homCochainComplexMap (F.map f).τ₁ g ≫ homCochainComplexMap (F.map f').τ₁ g' =
      homCochainComplexMap (F.map (f' ≫ f)).τ₁ (g ≫ g')
    rw [homCochainComplexMap_comp]
    have h : (F.map (f' ≫ f)).τ₁ = (F.map f').τ₁ ≫ (F.map f).τ₁ :=
      congrArg (fun t : F.obj P'' ⟶ F.obj P => t.τ₁) hF
    exact (congrArg (fun u : cyclesZeroComplex P'' ⟶ cyclesZeroComplex P =>
      homCochainComplexMap u (g ≫ g')) h).symm

/-- Point splittings assemble all product coordinates at one Hom degree. -/
def homCyclesDegreeSplitting (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (hB : ∀ r, Projective (Abelian.image (P.d r (r - 1)))) (n : ℤ) :
    ((homCyclesSequence P Q).map (eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n)).Splitting := by
  let S (r : ℤ) : ShortComplex C :=
    ShortComplex.mk (P.iCycles r) (Abelian.factorThruImage (P.d r ((ComplexShape.down ℤ).next r)))
      (by
        have h := (cyclesImageSequence P r ((ComplexShape.down ℤ).next r)).zero
        dsimp only [cyclesImageSequence] at h
        exact h)
  let point (r : ℤ) : (S r).Splitting := by
    have hn : (ComplexShape.down ℤ).next r = r - 1 :=
      (ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk _ _ (by omega))
    letI : Projective (Abelian.image (P.d r ((ComplexShape.down ℤ).next r))) := by
      rw [hn]
      exact hB r
    let t₀ := cyclesImageSequenceSplitting P r ((ComplexShape.down ℤ).next r) rfl
    dsimp only [cyclesImageSequence] at t₀
    exact t₀
  let ret :
      CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n →+
        CochainComplex.HomComplex.Cochain
          ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q n :=
    { toFun z := CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
        (point (-p)).s ≫ z.v p q hpq
      map_zero' := by
        funext T
        change (point (-T.p)).s ≫ 0 = 0
        exact CategoryTheory.Limits.comp_zero
      map_add' z z' := by
        funext T
        change (point (-T.p)).s ≫ (z T + z' T) =
          (point (-T.p)).s ≫ z T + (point (-T.p)).s ≫ z' T
        exact Preadditive.comp_add _ _ _ _ _ _ }
  let sec :
      CochainComplex.HomComplex.Cochain
          ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n →+
        CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence C).functor.obj P) Q n :=
    { toFun z := CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
        (point (-p)).r ≫ z.v p q hpq
      map_zero' := by
        funext T
        change (point (-T.p)).r ≫ 0 = 0
        exact CategoryTheory.Limits.comp_zero
      map_add' z z' := by
        funext T
        change (point (-T.p)).r ≫ (z T + z' T) =
          (point (-T.p)).r ≫ z T + (point (-T.p)).r ≫ z' T
        exact Preadditive.comp_add _ _ _ _ _ _ }
  refine
    { r := AddCommGrpCat.ofHom ret
      s := AddCommGrpCat.ofHom sec
      f_r := ?_
      s_g := ?_
      id := ?_ }
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    let z₀ : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj (outgoingImageZeroComplex P)) Q n := z
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    let t := point (-p)
    change t.s ≫ ((((homCyclesSequence P Q).f.f n).hom z₀).v p q hpq) = z₀.v p q hpq
    have h := homCyclesSequence_f_v P Q n p q hpq z₀
    let E := (homCyclesSequence P Q).map (eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n)
    have hId : (((𝟙 E.X₁ : E.X₁ ⟶ E.X₁).hom z).v p q hpq) = z₀.v p q hpq := rfl
    have ht : t.s ≫ (S (-p)).g ≫ z₀.v p q hpq = z₀.v p q hpq :=
      t.s_g_assoc (z₀.v p q hpq)
    exact (congrArg (fun x => t.s ≫ x) h).trans (ht.trans hId.symm)
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    let z₀ : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj (cyclesZeroComplex P)) Q n := z
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    let t := point (-p)
    have h := homCyclesSequence_g_v P Q n p q hpq (sec z₀)
    exact h.trans (by
      change (S (-p)).f ≫
        t.r ≫ z₀.v p q hpq = z₀.v p q hpq
      simpa only [Category.id_comp] using t.f_r_assoc (z₀.v p q hpq))
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    let z₀ : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence C).functor.obj P) Q n := z
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    let t := point (-p)
    have hF := homCyclesSequence_f_v P Q n p q hpq (ret z₀)
    have hG := homCyclesSequence_g_v P Q n p q hpq z₀
    have hG' := congrArg (fun x => t.r ≫ x) hG
    have hPoint :
        ((((homCyclesSequence P Q).f.f n).hom (ret z₀)).v p q hpq) +
          (sec (((homCyclesSequence P Q).g.f n).hom z₀)).v p q hpq =
        (S (-p)).g ≫
          (t.s ≫ z₀.v p q hpq) +
        t.r ≫ ((S (-p)).f ≫
          z₀.v p q hpq) := congrArg₂ (fun x y => x + y) hF hG'
    let v : P.X (-p) ⟶ Q.X q := z₀.v p q hpq
    have ht : (S (-p)).g ≫ t.s + t.r ≫ (S (-p)).f = 𝟙 (P.X (-p)) :=
      (add_comm _ _).trans t.id
    exact hPoint.trans (by
      change (S (-p)).g ≫ (t.s ≫ v) + t.r ≫ ((S (-p)).f ≫ v) = v
      simp only [← Category.assoc, ← Preadditive.add_comp, ht]
      exact Category.id_comp v)

/-- Projective outgoing images give the degreewise-exact full Hom sequence. -/
theorem homCyclesSequence_shortExact (P : ChainComplex C ℤ) (Q : CochainComplex C ℤ)
    (hB : ∀ r, Projective (Abelian.image (P.d r (r - 1)))) :
    (homCyclesSequence P Q).ShortExact := by
  exact @HomologicalComplex.shortExact_of_degreewise_shortExact
    AddCommGrpCat.{v} ℤ (ComplexShape.up ℤ) _ _ (homCyclesSequence P Q) (fun n => by
      let t := homCyclesDegreeSplitting P Q hB n
      exact ShortComplex.ShortExact.mk' t.exact t.mono_f t.epi_g)

end Abelian
end ChainComplex
