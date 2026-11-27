/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexAttachmentCompat
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.ConnectedSimplexTriviality
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary
public import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.OneCellCollarLocalTriviality

/-!
# Local products over finite connected simplicial bases

Let p:E→B be a minimal simplicial fibration in universe u, with B finite and connected, and
choose a vertex b₀ of B. Write F=|E×_B Δ[0]| for the realization of its strict simplicial fiber
over b₀. For every z∈|B|, there is an open neighborhood U containing z and an isomorphism
|E|×_{|B|}U≅U×F over U. Thus one fixed fiber gives local product charts throughout the realized
base.

The finite cell-attachment construction starts at a vertex and extends charts across successive
finite stages inside the connected ambient base.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Simplicial Opposite Topology
open scoped Simplicial

namespace SSet

private noncomputable def stagePullbackIso
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B B₀ B₁ : C}
    (p : E ⟶ B) (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B)
    (r : B₀ ⟶ B₁) (hr : r ≫ j₁ = j₀) :
    pullback p j₀ ≅ pullback (pullback.snd p j₁) r := by
  let sqNested : IsPullback
      (pullback.fst (pullback.snd p j₁) r ≫ pullback.fst p j₁)
      (pullback.snd (pullback.snd p j₁) r) p j₀ := by
    rw [← hr]
    exact (IsPullback.of_hasPullback (pullback.snd p j₁) r).paste_horiz
      (IsPullback.of_hasPullback p j₁)
  exact (IsPullback.of_hasPullback p j₀).isoIsPullback E B₀ sqNested

@[reassoc]
private theorem stagePullbackIso_hom_snd
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B B₀ B₁ : C}
    (p : E ⟶ B) (j₀ : B₀ ⟶ B) (j₁ : B₁ ⟶ B)
    (r : B₀ ⟶ B₁) (hr : r ≫ j₁ = j₀) :
    (stagePullbackIso p j₀ j₁ r hr).hom ≫
        pullback.snd (pullback.snd p j₁) r =
      pullback.snd p j₀ := by
  apply IsPullback.isoIsPullback_hom_snd

private noncomputable def pullbackIdIso
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B : C} (p : E ⟶ B) : pullback p (𝟙 B) ≅ E :=
  (IsPullback.of_hasPullback p (𝟙 B)).isoIsPullback E B
    IsPullback.of_id_fst

@[reassoc]
private theorem pullbackIdIso_hom_snd
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {E B : C} (p : E ⟶ B) :
    (pullbackIdIso p).hom ≫ p = pullback.snd p (𝟙 B) := by
  apply IsPullback.isoIsPullback_hom_snd

private noncomputable def vertexBaseIso {B : SSet.{u}}
    (b₀ : B _⦋0⦌) :
    (Subcomplex.ofSimplex b₀ : SSet.{u}) ≅ (Δ[0] : SSet.{u}) :=
  (Subcomplex.isTerminalOfSimplex b₀).uniqueUpToIso
    stdSimplex.isTerminalObj₀

@[reassoc]
private theorem vertexBaseIso_hom_const {B : SSet.{u}}
    (b₀ : B _⦋0⦌) :
    (vertexBaseIso b₀).hom ≫
        SSet.const (X := (Δ[0] : SSet.{u})) b₀ =
      (Subcomplex.ofSimplex b₀).ι := by
  rw [Subcomplex.ofSimplex_ι]
  simp

private noncomputable def initialSimplicialBundle
    {E B : SSet.{u}} [B.IsConnected]
    (p : E ⟶ B) (hp : MinimalFibration.IsMinimalFibration p)
    (b₀ : B _⦋0⦌) :
    TrivialBundleWithFiber
      (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
      (pullback.snd p (Subcomplex.ofSimplex b₀).ι) := by
  let c : (Δ[0] : SSet.{u}) ⟶ B := SSet.const b₀
  let qF := pullback.snd p c
  let hF := MinimalFibration.trivialBundleWithFiber_pullback_stdSimplex
    p hp b₀ c
  let e := stagePullbackIso p (Subcomplex.ofSimplex b₀).ι c
    (vertexBaseIso b₀).hom (vertexBaseIso_hom_const b₀)
  let hIter := hF.pullback
    (IsPullback.of_hasPullback qF (vertexBaseIso b₀).hom)
  exact TrivialBundleWithFiber.ofIso e
    (stagePullbackIso_hom_snd p _ _ _ _) hIter

private noncomputable def toTopTrivialBundleWithFiberOfFiniteBase
    {F E K : SSet.{u}} [K.Finite] {q : E ⟶ K}
    (h : TrivialBundleWithFiber F q) :
    TrivialBundleWithFiber (SSet.toTop.obj F) (SSet.toTop.map q) := by
  let chartS :=
    IsLimit.conePointUniqueUpToIso h.isLimit (prodIsProd K F)
  let _ : IsIso (prodComparison SSet.toTop K F) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary K F
  let chartT : SSet.toTop.obj E ≅
      SSet.toTop.obj K ⨯ SSet.toTop.obj F :=
    SSet.toTop.mapIso chartS ≪≫
      asIso (prodComparison SSet.toTop K F)
  let hProd : TrivialBundleWithFiber
      (SSet.toTop.obj F)
      (prod.fst : SSet.toTop.obj K ⨯ SSet.toTop.obj F ⟶
        SSet.toTop.obj K) :=
    { r := prod.snd
      isLimit := prodIsProd _ _ }
  apply TrivialBundleWithFiber.ofIso chartT _ hProd
  change (SSet.toTop.map chartS.hom ≫
      prodComparison SSet.toTop K F) ≫ prod.fst = SSet.toTop.map q
  rw [Category.assoc, prodComparison_fst]
  rw [← SSet.toTop.map_comp]
  congr 1
  exact h.isLimit.conePointUniqueUpToIso_hom_comp (prodIsProd K F)
    ⟨WalkingPair.left⟩

private noncomputable def overUnivOfTrivial
    {F E B : TopCat.{u}} {q : E ⟶ B}
    (h : TrivialBundleWithFiber F q) :
    MorphismProperty.TrivialBundleWithFiberOver F q
      (AlgebraicTopology.subspaceIncl (Set.univ : Set B)) where
  E' := pullback q (AlgebraicTopology.subspaceIncl Set.univ)
  p' := pullback.snd q (AlgebraicTopology.subspaceIncl Set.univ)
  t := pullback.fst q (AlgebraicTopology.subspaceIncl Set.univ)
  sq := IsPullback.of_hasPullback q
    (AlgebraicTopology.subspaceIncl Set.univ)
  trivial := h.pullback
    (IsPullback.of_hasPullback q
      (AlgebraicTopology.subspaceIncl Set.univ))

private noncomputable def overAmbientIso
    {F E E' B B' : TopCat.{u}}
    {p : E ⟶ B} {p' : E' ⟶ B}
    (e : E ≅ E') (he : e.hom ≫ p' = p)
    {f : B' ⟶ B}
    (h : MorphismProperty.TrivialBundleWithFiberOver F p f) :
    MorphismProperty.TrivialBundleWithFiberOver F p' f where
  E' := h.E'
  p' := h.p'
  t := h.t ≫ e.hom
  sq := h.sq.paste_horiz
    (IsPullback.of_horiz_isIso
      (fst := e.hom) (snd := p) (f := p') (g := 𝟙 B)
      ⟨by simpa using he⟩)
  trivial := h.trivial

private theorem pointLocal_iff_of_ambientIso
    {F E E' B : TopCat.{u}}
    {p : E ⟶ B} {p' : E' ⟶ B}
    (e : E ≅ E') (he : e.hom ≫ p' = p) (z : B) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality p F z ↔
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality p' F z := by
  constructor
  · rintro ⟨U, hU, hz, h⟩
    exact ⟨U, hU, hz, h.map (overAmbientIso e he)⟩
  · rintro ⟨U, hU, hz, h⟩
    have he' : e.inv ≫ p = p' := by
      rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact ⟨U, hU, hz, h.map (overAmbientIso e.symm he')⟩

private theorem initialPointLocal
    {E B : SSet.{u}} [B.IsConnected]
    (p : E ⟶ B) (hp : MinimalFibration.IsMinimalFibration p)
    (b₀ : B _⦋0⦌) :
    ∀ x : SSet.toTop.obj (Subcomplex.ofSimplex b₀ : SSet.{u}),
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map
          (pullback.snd p (Subcomplex.ofSimplex b₀).ι))
        (SSet.toTop.obj
          (pullback p
            (SSet.const (X := (Δ[0] : SSet.{u})) b₀))) x := by
  intro x
  let hS := initialSimplicialBundle p hp b₀
  let hT := toTopTrivialBundleWithFiberOfFiniteBase hS
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ x,
    ⟨overUnivOfTrivial hT⟩⟩

private def terminalSubcomplexIso {B : SSet.{u}} (C : B.Subcomplex)
    (hC : C = ⊤) : (C : SSet.{u}) ≅ B :=
  Subcomplex.eqToIso hC ≪≫ Subcomplex.topIso B

@[reassoc]
private theorem terminalSubcomplexIso_hom {B : SSet.{u}}
    (C : B.Subcomplex) (hC : C = ⊤) :
    (terminalSubcomplexIso C hC).hom = C.ι := by
  simp [terminalSubcomplexIso]

private theorem terminalPushout
    {B : SSet.{u}} {C₀ C₁ : B.Subcomplex}
    {n : ℕ}
    (t : (SSet.boundary n : SSet.{u}) ⟶ (C₀ : SSet.{u}))
    (hle : C₀ ≤ C₁)
    (b : (Δ[n] : SSet.{u}) ⟶ (C₁ : SSet.{u}))
    (sq : IsPushout t (SSet.boundary n).ι
      (Subcomplex.homOfLE hle) b)
    (hTop : C₁ = ⊤) :
    IsPushout t (SSet.boundary n).ι
      (Subcomplex.homOfLE hle ≫
        (terminalSubcomplexIso C₁ hTop).hom)
      (b ≫ (terminalSubcomplexIso C₁ hTop).hom) := by
  apply sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (terminalSubcomplexIso C₁ hTop)
  · simp
  · simp
  · simp
  · simp

private theorem terminalOldMap
    {B : SSet.{u}} {C₀ C₁ : B.Subcomplex}
    (hle : C₀ ≤ C₁) (hTop : C₁ = ⊤) :
    (Subcomplex.homOfLE hle ≫
        (terminalSubcomplexIso C₁ hTop).hom) ≫
      𝟙 B = C₀.ι := by
  rw [Category.comp_id, terminalSubcomplexIso_hom,
    Subcomplex.homOfLE_ι]

private noncomputable def terminalBaseSimplicialBundle
    {E B : SSet.{u}} [B.IsConnected]
    (p : E ⟶ B) (hp : MinimalFibration.IsMinimalFibration p)
    (b₀ : B _⦋0⦌)
    (hTop : Subcomplex.ofSimplex b₀ = ⊤) :
    TrivialBundleWithFiber
      (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
      (pullback.snd p (𝟙 B)) := by
  let eTop := terminalSubcomplexIso (Subcomplex.ofSimplex b₀) hTop
  let hBT : IsTerminal B :=
    (Subcomplex.isTerminalOfSimplex b₀).ofIso eTop
  let eB : B ≅ (Δ[0] : SSet.{u}) :=
    hBT.uniqueUpToIso stdSimplex.isTerminalObj₀
  let c : (Δ[0] : SSet.{u}) ⟶ B := SSet.const b₀
  have heB : eB.hom ≫ c = 𝟙 B := hBT.hom_ext _ _
  let hF := MinimalFibration.trivialBundleWithFiber_pullback_stdSimplex
    p hp b₀ c
  let e := stagePullbackIso p (𝟙 B) c eB.hom heB
  let hIter := hF.pullback
    (IsPullback.of_hasPullback (pullback.snd p c) eB.hom)
  exact TrivialBundleWithFiber.ofIso e
    (stagePullbackIso_hom_snd p _ _ _ _) hIter

private theorem oneCellPointLocal_to_opens
    {E B F : TopCat.{u}} (q : E ⟶ B) (z : B)
    (h : TopCat.modelCategoryQuillen.OneCellPointLocalTriviality q F z) :
    ∃ U : TopologicalSpace.Opens B, z ∈ U ∧
      Nonempty
        (MorphismProperty.TrivialBundleWithFiberOver
          F q (AlgebraicTopology.subspaceIncl U)) := by
  obtain ⟨U, hU, hz, htriv⟩ := h
  exact ⟨⟨U, hU⟩, hz, htriv⟩

private theorem terminalPointLocal_to_ambient
    {E B : SSet.{u}} (p : E ⟶ B) (F : TopCat.{u})
    (z : SSet.toTop.obj B)
    (h : TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map (pullback.snd p (𝟙 B))) F z) :
    TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
      (SSet.toTop.map p) F z := by
  let e := SSet.toTop.mapIso (pullbackIdIso p)
  have he : e.hom ≫ SSet.toTop.map p =
      SSet.toTop.map (pullback.snd p (𝟙 B)) := by
    change SSet.toTop.map (pullbackIdIso p).hom ≫
      SSet.toTop.map p = _
    rw [← SSet.toTop.map_comp, pullbackIdIso_hom_snd]
  exact (pointLocal_iff_of_ambientIso e he z).mp h

/-- Let p:E→B be a minimal simplicial fibration in universe u, with B finite and connected, and
choose a vertex b₀ of B. Write F=|E×_B Δ[0]| for the realization of its strict simplicial fiber
over b₀. For every z∈|B| there is an open U⊆|B| with z∈U and a product trivialization
|E|×_\{|B|\}U≅U×F over U. The comparison is over the open-subspace inclusion U→|B| and uses the
realization of the simplicial fiber, with b₀ the chosen ambient vertex. -/
theorem exists_local_trivialBundleWithFiber_toTop
    {E B : SSet.{u}} [B.Finite] [B.IsConnected]
    (p : E ⟶ B)
    (hp : MinimalFibration.IsMinimalFibration p)
    (b₀ : B _⦋0⦌) (z : SSet.toTop.obj B) :
    ∃ U : TopologicalSpace.Opens (SSet.toTop.obj B), z ∈ U ∧
      Nonempty
        (MorphismProperty.TrivialBundleWithFiberOver
          (SSet.toTop.obj
            (pullback p
              (SSet.const (X := (Δ[0] : SSet.{u})) b₀)))
          (SSet.toTop.map p)
          (AlgebraicTopology.subspaceIncl U)) := by
  let A₀ : B.Subcomplex := Subcomplex.ofSimplex b₀
  let FTop := SSet.toTop.obj
    (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
  let StageProp : B.Subcomplex → Prop := fun D =>
    ∀ x : SSet.toTop.obj (D : SSet.{u}),
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map (pullback.snd p D.ι)) FTop x
  obtain ⟨k, C, hC₀, hCk, _hMono, hStep⟩ :=
    boundary.exists_finite_attachment_chain_of_le_of_finite
      A₀ ⊤ le_top
  have hInitial : StageProp A₀ := by
    simpa only [StageProp, A₀, FTop] using initialPointLocal p hp b₀
  have hIdentity : ∀ y : SSet.toTop.obj B,
      TopCat.modelCategoryQuillen.OneCellPointLocalTriviality
        (SSet.toTop.map (pullback.snd p (𝟙 B))) FTop y := by
    cases k with
    | zero =>
        have hTop : Subcomplex.ofSimplex b₀ = (⊤ : B.Subcomplex) := by
          exact hC₀.symm.trans hCk
        let hS := terminalBaseSimplicialBundle p hp b₀ hTop
        let hT := toTopTrivialBundleWithFiberOfFiniteBase hS
        intro y
        exact ⟨Set.univ, isOpen_univ, Set.mem_univ y,
          ⟨overUnivOfTrivial hT⟩⟩
    | succ k =>
        have hStage : ∀ (i : ℕ) (hi : i < k + 1),
            StageProp
              (C ⟨i, Nat.lt_trans hi (Nat.lt_succ_self (k + 1))⟩) := by
          intro i
          induction i with
          | zero =>
              intro hi
              simpa only [hC₀] using hInitial
          | succ i ih =>
              intro hi
              have hi' : i < k + 1 :=
                Nat.lt_trans (Nat.lt_succ_self i) hi
              obtain ⟨n, t, b, hle, hsq, _hlt, _hleTop⟩ :=
                hStep i hi'
              have hPrev := ih hi'
              dsimp only [StageProp] at hPrev ⊢
              exact MinimalFibration.oneCellPointLocal_all_of_old_ambient
                p hp b₀
                (C ⟨i, Nat.lt_trans hi'
                  (Nat.lt_succ_self (k + 1))⟩).ι
                (C ⟨i + 1, Nat.succ_lt_succ hi'⟩).ι
                t (Subcomplex.homOfLE hle) b
                (Subcomplex.homOfLE_ι hle) hsq hPrev
        have hk : k < k + 1 := Nat.lt_succ_self k
        obtain ⟨n, t, b, hle, hsq, _hlt, _hleTop⟩ := hStep k hk
        let C₀ := C ⟨k, Nat.lt_trans hk
          (Nat.lt_succ_self (k + 1))⟩
        let C₁ := C ⟨k + 1, Nat.succ_lt_succ hk⟩
        have hTop : C₁ = (⊤ : B.Subcomplex) := by
          simpa only [C₁] using hCk
        let rB : (C₀ : SSet.{u}) ⟶ B :=
          Subcomplex.homOfLE hle ≫
            (terminalSubcomplexIso C₁ hTop).hom
        let bB : (Δ[n] : SSet.{u}) ⟶ B :=
          b ≫ (terminalSubcomplexIso C₁ hTop).hom
        have hsqB : IsPushout t (SSet.boundary n).ι rB bB :=
          terminalPushout t hle b hsq hTop
        have hjB : rB ≫ 𝟙 B = C₀.ι :=
          terminalOldMap hle hTop
        have hPrev : StageProp C₀ := by
          simpa only [C₀] using hStage k hk
        dsimp only [StageProp] at hPrev
        intro y
        exact MinimalFibration.oneCellPointLocal_all_of_old_ambient
          p hp b₀ C₀.ι (𝟙 B) t rB bB hjB hsqB hPrev y
  have hAmbient := terminalPointLocal_to_ambient p FTop z (hIdentity z)
  simpa only [FTop] using
    oneCellPointLocal_to_opens (SSet.toTop.map p) z hAmbient

end SSet
