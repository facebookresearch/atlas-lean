/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointPrismFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningCartesianExistence

/-!
# Whole original boundary endpoint prisms for actual native model maps

The original endpoint, increasing prism filtration, marked boundary
verticals and all original base equations are retained. Actual native
inner/critical lifts extend the positive-dimensional whole prism, and
the original marked endpoint lift handles degree zero. No intrinsic
Cartesian-fibration assumption on the native map is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- All verticals are the same original vertical-one simplices, marked in the unchanged native total object. -/
def nativePrismOneVerticalsMarked (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ)
    {T : SSet.{u}} (L : T ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet) : Prop :=
  ∀ x : T _⦋0⦌, L.app (op ⦋1⦌) (verticalOneSimplex x) ∈ (nativeUnstraighteningTotal B F).marking

/-- Positive-dimensional original scalar boundaries retain whole target-prescribed native prism extension and all
original marked verticals. -/
theorem nativeUnstraightening_endpointPrism_boundary_positive (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) {n : ℕ} (hn : 1 ≤ n)
    (H : (boundary.{u} n : SSet.{u}) ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (c : (Δ[n] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet)
    (hHsrc : prismSectionAt (boundary.{u} n : SSet.{u}) 1 ≫ H = (boundary.{u} n).ι ≫ c)
    (hKsrc : prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ K = c ≫ ((nativeUnstraightening B).map q).left.hom)
    (hHK : H ≫ ((nativeUnstraightening B).map q).left.hom = ((boundary.{u} n).ι ▷ (Δ[1] : SSet.{u})) ≫ K)
    (hHvert : nativePrismOneVerticalsMarked B F H) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∃ L : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      ((boundary.{u} n).ι ▷ (Δ[1] : SSet.{u})) ≫ L = H ∧
        prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ L = c ∧
        L ≫ ((nativeUnstraightening B).map q).left.hom = K ∧ nativePrismOneVerticalsMarked B F L := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let X := (nativeUnstraighteningTotal B F).toSSet
  let p : (nativeUnstraighteningTotal B F).toSSet ⟶ (nativeUnstraighteningTotal B G).toSSet :=
    ((nativeUnstraightening B).map q).left.hom
  let face1 : (Δ[1] : SSet.{u}).Subcomplex :=
    SSet.stdSimplex.face {1}
  set cface : Δ[n] ⊗ (face1 : SSet.{u}) ⟶ X :=
    CartesianMonoidalCategory.fst _ _ ≫ c with hcface
  have hw : (∂Δ[n].ι ▷ (face1 : SSet.{u})) ≫ cface =
      ((∂Δ[n] : SSet.{u}) ◁ face1.ι) ≫ H := by
    calc (∂Δ[n].ι ▷ (face1 : SSet.{u})) ≫ cface
        = (CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            ∂Δ[n].ι) ≫ c := by
          rw [hcface, ← Category.assoc]
          congr 1
      _ = CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            (prismSectionAt (∂Δ[n] : SSet.{u}) 1 ≫ H) := by
          rw [Category.assoc, ← hHsrc]
      _ = ((∂Δ[n] : SSet.{u}) ◁ face1.ι) ≫ H := by
          dsimp only [face1]
          rw [whiskerLeft_faceOne_ι, Category.assoc]
  let sq := Subcomplex.unionProd.isPushout ∂Δ[n] face1
  let φ₀ := sq.desc cface H hw
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n] face1 ≫ φ₀ = cface :=
    sq.inl_desc cface H hw
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n] face1 ≫ φ₀ = H :=
    sq.inr_desc cface H hw
  have hcfaceBase : cface ≫ p = (Δ[n] ◁ face1.ι) ≫ K := by
    have hg : CartesianMonoidalCategory.fst (Δ[n] : SSet.{u}) (face1 : SSet.{u}) ≫
        prismSectionAt (Δ[n] : SSet.{u}) 1 = Δ[n] ◁ face1.ι := by
      dsimp only [face1]
      rw [whiskerLeft_faceOne_ι]
    exact (congrArg (fun f => f ≫ p) hcface).trans
      ((Category.assoc (CartesianMonoidalCategory.fst Δ[n] (face1 : SSet.{u})) c p).trans
        ((congrArg (fun f => CartesianMonoidalCategory.fst Δ[n] (face1 : SSet.{u}) ≫ f) hKsrc.symm).trans
          ((Category.assoc (CartesianMonoidalCategory.fst Δ[n] (face1 : SSet.{u})) (prismSectionAt Δ[n] 1) K).symm.trans
            (congrArg (fun f => f ≫ K) hg))))
  have hι₁ι : Subcomplex.unionProd.ι₁ ∂Δ[n] face1 ≫
        (prismTgtInitial n).ι = Δ[n] ◁ face1.ι := by
    dsimp only [face1, prismTgtInitial]
    exact Subcomplex.unionProd.ι₁_ι ∂Δ[n] (stdSimplex.face {1})
  have hι₂ι : Subcomplex.unionProd.ι₂ ∂Δ[n] face1 ≫
        (prismTgtInitial n).ι = ∂Δ[n].ι ▷ Δ[1] := by
    dsimp only [face1, prismTgtInitial]
    exact Subcomplex.unionProd.ι₂_ι ∂Δ[n] (stdSimplex.face {1})
  have hbase₀ : φ₀ ≫ p =
      (prismTgtInitial n).ι ≫ K := by
    apply sq.hom_ext
    · exact (Category.assoc (Subcomplex.unionProd.ι₁ ∂Δ[n] face1) φ₀ p).symm.trans
        ((congrArg (fun f => f ≫ p) hι₁).trans
          (hcfaceBase.trans ((congrArg (fun f => f ≫ K) hι₁ι.symm).trans
            (Category.assoc (Subcomplex.unionProd.ι₁ ∂Δ[n] face1) (prismTgtInitial n).ι K))))
    · exact (Category.assoc (Subcomplex.unionProd.ι₂ ∂Δ[n] face1) φ₀ p).symm.trans
        ((congrArg (fun f => f ≫ p) hι₂).trans
          (hHK.trans ((congrArg (fun f => f ≫ K) hι₂ι.symm).trans
            (Category.assoc (Subcomplex.unionProd.ι₂ ∂Δ[n] face1) (prismTgtInitial n).ι K))))
  let x0b : (∂Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk 0)) :=
    ⟨stdSimplex.obj₀Equiv.symm (Fin.last n),
      vertex_mem_boundary_of_one_le hn _⟩
  have happ2 : (Subcomplex.unionProd.ι₂ ∂Δ[n] face1).app _
        (verticalOneSimplex x0b) =
      ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ := by
    apply Subtype.ext
    change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex x0b) =
      prismVertLast n
    have happx : ∂Δ[n].ι.app _ x0b = stdSimplex.obj₀Equiv.symm (Fin.last n) := rfl
    rw [whiskerRight_app_verticalOneSimplex, happx]
    apply Prod.ext
    · apply stdSimplex.ext
      intro t
      fin_cases t <;> rfl
    · apply stdSimplex.ext
      intro t
      fin_cases t <;> rfl
  have hcriticalEdge : φ₀.app _ ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ =
      H.app _ (verticalOneSimplex x0b) := by
    rw [← happ2]
    exact congr($(hι₂).app _ (verticalOneSimplex x0b))
  have hcritical : φ₀.app (op ⦋1⦌) ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ ∈
      (nativeUnstraighteningTotal B F).marking := hcriticalEdge.symm ▸ hHvert x0b
  obtain ⟨L, hF, hFbase⟩ := nativeUnstraightening_endpointPrism_entire B q hn φ₀ K hbase₀ hcritical hq
  refine ⟨L, ?_, ?_, hFbase, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[1]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] face1 ≫
          (prismTgtInitial n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n] face1).symm
    rw [e₂, Category.assoc, hF, hι₂]
  · apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    have hmemFace : ((prismSectionAt Δ[n] (1 : Fin 2)).app U s).2 ∈
        face1.obj U := by
      subst face1
      change Finset.image
          (stdSimplex.objEquiv
            (((prismSectionAt Δ[n] (1 : Fin 2)).app U s).2)).toOrderHom
            ⊤ ≤ ({1} : Finset (Fin 2))
      rw [Finset.image_subset_iff]
      intro j _
      exact Finset.mem_singleton.2
        (asOrderHom_prismSectionAt_app_snd Δ[n] (1 : Fin 2) s j)
    have hmem : (prismSectionAt Δ[n] 1).app U s ∈
        (prismTgtInitial n).obj U :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl hmemFace)
    let sface : (Δ[n] ⊗ (face1 : SSet.{u})).obj U :=
      (s, ⟨((prismSectionAt Δ[n] 1).app U s).2, hmemFace⟩)
    have happ1 : (Subcomplex.unionProd.ι₁ ∂Δ[n] face1).app U sface =
        ⟨(prismSectionAt Δ[n] 1).app U s, hmem⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact (prismSectionAt_app_fst _ _ s).symm
      · rfl
    change L.app U ((prismSectionAt Δ[n] 1).app U s) = c.app U s
    calc L.app U ((prismSectionAt Δ[n] 1).app U s)
        = φ₀.app U ⟨(prismSectionAt Δ[n] 1).app U s, hmem⟩ :=
          congr($(hF).app U ⟨(prismSectionAt Δ[n] 1).app U s, hmem⟩)
      _ = cface.app U sface := by
          rw [← happ1]
          exact congr($(hι₁).app U sface)
      _ = c.app U s := rfl
  · intro x
    let xb : (∂Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk 0)) :=
      ⟨x, vertex_mem_boundary_of_one_le hn x⟩
    have hmemV : verticalOneSimplex x ∈ (prismTgtInitial n).obj _ :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr (by
        rw [verticalOneSimplex_fst]
        exact sigma_zero_mem_boundary_of_one_le hn x))
    have happ2' : (Subcomplex.unionProd.ι₂ ∂Δ[n] face1).app _
          (verticalOneSimplex xb) = ⟨verticalOneSimplex x, hmemV⟩ := by
      apply Subtype.ext
      change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex xb) =
        verticalOneSimplex x
      rw [whiskerRight_app_verticalOneSimplex]
      rfl
    have hedge : L.app _ (verticalOneSimplex x) = H.app _ (verticalOneSimplex xb) := by
      calc L.app _ (verticalOneSimplex x)
          = φ₀.app _ ⟨verticalOneSimplex x, hmemV⟩ :=
            congr($(hF).app _ ⟨verticalOneSimplex x, hmemV⟩)
        _ = H.app _ (verticalOneSimplex xb) := by
            rw [← happ2']
            exact congr($(hι₂).app _ (verticalOneSimplex xb))
    exact hedge.symm ▸ hHvert xb



/-- Actual coherent-model fibrations retain the original marked endpoint lift on the same full native total map. -/
theorem nativeUnstraightening_map_originalMarkedEndpointLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty cartesianEndpointCell.{u} ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  have hOver := nativeUnstraightening_map_originalCartesianEndpointRlp B q hq
  have h : (ofHoms (fun s : Unit => (nativeOriginalCartesianEndpoint.{u} s).hom)).rlp
      ((nativeUnstraightening B).map q).left :=
    (overCells_rlp_iff nativeOriginalCartesianEndpoint.{u} (max B) ((nativeUnstraightening B).map q)).mp hOver
  exact h _ (ofHoms.mk (f := fun s : Unit => (nativeOriginalCartesianEndpoint.{u} s).hom) ())

private theorem nativePrismSectionAt_zero_target :
    prismSectionAt (Δ[0] : SSet.{u}) (1 : Fin 2) =
      stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv := by
  apply yonedaEquiv.injective
  apply Prod.ext
  · apply yonedaEquiv.symm.injective
    exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · apply stdSimplex.obj₀Equiv.injective
    rfl

private theorem nativePrismVertical_zero :
    yonedaEquiv.symm
      (verticalOneSimplex (B := (Δ[0] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)) =
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv := by
  apply CartesianMonoidalCategory.hom_ext
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · have hleft : yonedaEquiv.symm
        (verticalOneSimplex (B := (Δ[0] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)) ≫
          CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    have hright : (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
        CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := rfl
    rw [hleft, hright]

/-- Degree zero uses the same actual marked endpoint cell to retain the whole native prism, target point and
original marked vertical. -/
theorem nativeUnstraightening_endpointPrism_boundary_zero (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G)
    (H : (boundary.{u} 0 : SSet.{u}) ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (c : (Δ[0] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (K : prod (max (Δ[0] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B G)
    (hKsrc : prismSectionAt (Δ[0] : SSet.{u}) 1 ≫ K.hom = c ≫ ((nativeUnstraightening B).map q).left.hom) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∃ L : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      ((boundary.{u} 0).ι ▷ (Δ[1] : SSet.{u})) ≫ L = H ∧
        prismSectionAt (Δ[0] : SSet.{u}) 1 ≫ L = c ∧
        L ≫ ((nativeUnstraightening B).map q).left.hom = K.hom ∧ nativePrismOneVerticalsMarked B F L := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p : nativeUnstraighteningTotal B F ⟶ nativeUnstraighteningTotal B G :=
    ((nativeUnstraightening B).map q).left
  let b : max (Δ[1] : SSet.{u}) ⟶ nativeUnstraighteningTotal B G :=
    { hom := (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K.hom
      preserve {e} _ := K.preserve (show
        (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv.app (op ⦋1⦌) e ∈
          (prod (max (Δ[0] : SSet.{u})) (max (Δ[1] : SSet.{u}))).marking from
        ⟨Set.mem_univ _, Set.mem_univ _⟩) }
  let a : min (Δ[0] : SSet.{u}) ⟶ nativeUnstraighteningTotal B F := ofMin c
  let sq : CommSq a cartesianEndpointCell.{u} p b := by
    constructor
    apply Hom.ext
    change c ≫ p.hom = stdSimplex.δ (0 : Fin 2) ≫
      ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K.hom)
    exact hKsrc.symm.trans ((congrArg (fun f => f ≫ K.hom) nativePrismSectionAt_zero_target).trans
      (Category.assoc _ _ _))
  obtain ⟨l, hl, hr⟩ := (nativeUnstraightening_map_originalMarkedEndpointLifting B q hq).sq_hasLift sq
  let L : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet :=
    (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom ≫ l.hom
  have hLbase : L ≫ p.hom = K.hom := by
    have hr' : l.hom ≫ p.hom = (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K.hom := congrArg Hom.hom hr
    exact (Category.assoc (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom l.hom p.hom).trans
      ((congrArg (fun f => (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom ≫ f) hr').trans
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom_inv_id_assoc K.hom))
  refine ⟨L, eq_of_boundaryZero_tensor _ _, ?_, hLbase, ?_⟩
  · have hsection : prismSectionAt (Δ[0] : SSet.{u}) 1 ≫
        (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom = stdSimplex.δ (0 : Fin 2) := by
      rw [nativePrismSectionAt_zero_target, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hpoint : stdSimplex.δ (0 : Fin 2) ≫ l.hom = c := congrArg Hom.hom hl
    exact (Category.assoc (prismSectionAt (Δ[0] : SSet.{u}) 1)
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom l.hom).symm.trans
        ((congrArg (fun f => f ≫ l.hom) hsection).trans hpoint)
  · intro x
    have hx : x = stdSimplex.obj₀Equiv.symm 0 := by
      apply yonedaEquiv.symm.injective
      exact stdSimplex.isTerminalObj₀.hom_ext _ _
    subst x
    have hvalue : L.app (op ⦋1⦌) (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) =
        yonedaEquiv l.hom := by
      let v := verticalOneSimplex (B := (Δ[0] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)
      have hvmap : yonedaEquiv.symm v ≫ L = l.hom :=
        (congrArg (fun f => f ≫ L) nativePrismVertical_zero).trans
          ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv_hom_id_assoc l.hom)
      have hv : yonedaEquiv (yonedaEquiv.symm v) = v := Equiv.apply_symm_apply _ _
      exact (congrArg (fun e => L.app (op ⦋1⦌) e) hv.symm).trans
        ((yonedaEquiv_comp (yonedaEquiv.symm v) L).symm.trans (congrArg yonedaEquiv hvmap))
    exact hvalue.symm ▸ l.preserve (Set.mem_univ _)

/-- Every original scalar boundary retains its whole original marked-vertical native endpoint prism under an actual
coherent-model fibration. -/
theorem nativeUnstraightening_endpointPrism_boundary (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (n : ℕ)
    (H : (boundary.{u} n : SSet.{u}) ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (c : (Δ[n] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (K : prod (max (Δ[n] : SSet.{u})) (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B G)
    (hHsrc : prismSectionAt (boundary.{u} n : SSet.{u}) 1 ≫ H = (boundary.{u} n).ι ≫ c)
    (hKsrc : prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ K.hom = c ≫ ((nativeUnstraightening B).map q).left.hom)
    (hHK : H ≫ ((nativeUnstraightening B).map q).left.hom = ((boundary.{u} n).ι ▷ (Δ[1] : SSet.{u})) ≫ K.hom)
    (hHvert : nativePrismOneVerticalsMarked B F H) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∃ L : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      ((boundary.{u} n).ι ▷ (Δ[1] : SSet.{u})) ≫ L = H ∧
        prismSectionAt (Δ[n] : SSet.{u}) 1 ≫ L = c ∧
        L ≫ ((nativeUnstraightening B).map q).left.hom = K.hom ∧ nativePrismOneVerticalsMarked B F L := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  by_cases hn : n = 0
  · subst n
    exact nativeUnstraightening_endpointPrism_boundary_zero B q H c K hKsrc hq
  · exact nativeUnstraightening_endpointPrism_boundary_positive B q (Nat.one_le_iff_ne_zero.mpr hn)
      H c K.hom hHsrc hKsrc hHK hHvert hq

end SSet.Marked
