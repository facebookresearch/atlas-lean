/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplexCategory.AbsoluteCofacePullbacks
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

/-!
# Original coface colimits and mapped simplicial boundaries

The original cofaces of a simplex of dimension at least two form a colimit
in their literal union under every Type-valued functor on the simplex category.
The doubleface relations are the original simplex operators.

Applying a functor on simplicial sets that preserves finite colimits gives
coverage of every positive-dimensional boundary by its original represented
faces. The zero boundary and the two endpoint coproduct use their actual
initial and coproduct diagrams. These are the finite diagrams used in Joyal,
*The theory of quasi-categories*, D.0.9 and D.0.28.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory Limits
open scoped Simplicial

namespace SimplexCategory

/-- The original cofaces and their ordered doublefaces. -/
def cofaceMultispan (H : SimplexCategory ⥤ Type v) (n : ℕ) :
    MultispanIndex (.ofLinearOrder (Fin (n + 3))) (Type v) where
  left _ := H.obj ⦋n⦌
  right _ := H.obj ⦋n + 1⦌
  fst p := H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2)))
  snd p := H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2)))

/-- The actual union of the original coface ranges. -/
def cofaceRangeUnion (H : SimplexCategory ⥤ Type v) (n : ℕ) : Type v :=
  { x : H.obj ⦋n + 2⦌ //
      ∃ i : Fin (n + 3), ∃ a : H.obj ⦋n + 1⦌, H.map (δ i) a = x }

/-- The original coface maps into their literal range union. -/
def cofaceUnionCocone (H : SimplexCategory ⥤ Type v) (n : ℕ) :
    Multicofork (cofaceMultispan H n) :=
  Multicofork.ofπ _ (cofaceRangeUnion H n)
    (fun i ↦ ↾fun a ↦ ⟨H.map (δ i) a, i, a, rfl⟩) (fun p ↦ by
      ext a
      apply Subtype.ext
      let i := p.1.1.castPred (Fin.ne_last_of_lt p.2)
      have hi : i.castSucc = p.1.1 := Fin.ext rfl
      have hp : p.1.1 < p.1.2 := p.2
      have h : i.castSucc < p.1.2 := by simpa only [hi] using hp
      change (H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫
        H.map (δ p.1.1)) a = (H.map (δ i) ≫ H.map (δ p.1.2)) a
      rw [← H.map_comp, ← H.map_comp]
      have hd : δ i ≫ δ p.1.2 =
          δ (p.1.2.pred (Fin.ne_zero_of_lt p.2)) ≫ δ p.1.1 := by
        simpa only [hi] using δ_comp_δ' h
      rw [hd])

@[simp]
theorem cofaceUnionCocone_π_val (H : SimplexCategory ⥤ Type v) (n : ℕ)
    (i : Fin (n + 3)) (a : H.obj ⦋n + 1⦌) :
    ((cofaceUnionCocone H n).π i a).val = H.map (δ i) a := rfl

/-- The original coface union is a colimit of the original doubleface diagram. -/
def cofaceUnionIsColimit (H : SimplexCategory ⥤ Type v) (n : ℕ) :
    IsColimit (cofaceUnionCocone H n) := by
  have injective (i : Fin (n + 3)) : Function.Injective (H.map (δ i)) := by
    let r : ⦋n + 2⦌ ⟶ ⦋n + 1⦌ := if hi : i = 0 then σ 0 else σ (i.pred hi)
    have hr : δ i ≫ r = 𝟙 _ := by
      dsimp only [r]
      split_ifs with hi
      · subst i
        exact δ_comp_σ_self (i := 0)
      · simpa only [Fin.succ_pred] using δ_comp_σ_succ (i := i.pred hi)
    apply Function.LeftInverse.injective (g := H.map r)
    intro a
    change (H.map (δ i) ≫ H.map r) a = a
    rw [← H.map_comp, hr, H.map_id]
    rfl
  have ordered {i j : Fin (n + 3)} (h : i < j) (a b : H.obj ⦋n + 1⦌)
      (hab : H.map (δ i) a = H.map (δ j) b) :
      (cofaceMultispan H n).multispan.ιColimitType (.right i) a =
        (cofaceMultispan H n).multispan.ιColimitType (.right j) b := by
    let i₀ := i.castPred (Fin.ne_last_of_lt h)
    have hi : i₀.castSucc = i := Fin.ext rfl
    have h₀ : i₀.castSucc < j := by simpa only [hi] using h
    obtain ⟨z, hz, _⟩ := existsUnique_cofaceFiller H i₀ j h₀ a b (by
      simpa only [hi] using hab)
    let p : (MultispanShape.ofLinearOrder (Fin (n + 3))).L := ⟨(i, j), h⟩
    let d := (cofaceMultispan H n).multispan
    have hf := d.ιColimitType_map (WalkingMultispan.Hom.fst p) z
    have hs := d.ιColimitType_map (WalkingMultispan.Hom.snd p) z
    have hfst : d.map (WalkingMultispan.Hom.fst p) z = a := hz.1
    have hsnd : d.map (WalkingMultispan.Hom.snd p) z = b := hz.2
    rw [hfst] at hf
    rw [hsnd] at hs
    exact hf.trans hs.symm
  apply Nonempty.some
  rw [Types.isColimit_iff_coconeTypesIsColimit,
    Functor.CoconeTypes.isMulticoequalizer_iff]
  refine ⟨?_, ?_⟩
  · intro i j a b hab
    have hab' : H.map (δ i) a = H.map (δ j) b := congrArg Subtype.val hab
    rcases lt_trichotomy (α := Fin (n + 3)) i j with h | h | h
    · exact ordered h a b hab'
    · subst j
      obtain rfl := injective i hab'
      rfl
    · exact (ordered h b a hab'.symm).symm
  · rintro ⟨x, i, a, ha⟩
    refine ⟨i, a, ?_⟩
    exact Subtype.ext ha

/-- Every compatible original face family has its unique original descendant. -/
theorem existsUnique_cofaceUnionDesc (H : SimplexCategory ⥤ Type v) (n : ℕ)
    (T : Type v) (a : Fin (n + 3) → (H.obj ⦋n + 1⦌ ⟶ T))
    (w : ∀ p : (MultispanShape.ofLinearOrder (Fin (n + 3))).L,
      (cofaceMultispan H n).fst p ≫ a p.1.1 =
        (cofaceMultispan H n).snd p ≫ a p.1.2) :
    ∃! f : cofaceRangeUnion H n ⟶ T, ∀ i, (cofaceUnionCocone H n).π i ≫ f = a i := by
  let hc := cofaceUnionIsColimit H n
  refine ⟨Multicofork.IsColimit.desc hc a w, ?_, ?_⟩
  · intro i
    exact Multicofork.IsColimit.fac hc a w i
  · intro f hf
    exact Multicofork.IsColimit.hom_ext hc (fun i ↦
      (hf i).trans (Multicofork.IsColimit.fac hc a w i).symm)

end SimplexCategory

namespace SSet

/-- The finite diagram of actual boundary faces and their actual intersections. -/
def boundaryMultispan (N : ℕ) :
    MultispanIndex (.ofLinearOrder (Fin (N + 1))) SSet.{u} :=
  let h : Subcomplex.MulticoequalizerDiagram (boundary.{u} N)
      (fun i : Fin (N + 1) ↦ stdSimplex.face {i}ᶜ)
      (fun i j ↦ stdSimplex.face {i, j}ᶜ) :=
    { iSup_eq := (boundary_eq_iSup N).symm
      eq_inf i j := by
        rw [stdSimplex.face_inter_face]
        congr 1
        ext k
        simp }
  h.multispanIndex.toLinearOrder.map Subcomplex.toSSetFunctor

/-- Apply the given functor to the original finite boundary multicofork. -/
def mappedBoundaryCocone (F : SSet.{u} ⥤ Type v) (N : ℕ) :
    Multicofork ((boundaryMultispan N).map F) :=
  let h : Subcomplex.MulticoequalizerDiagram (boundary.{u} N)
      (fun i : Fin (N + 1) ↦ stdSimplex.face {i}ᶜ)
      (fun i j ↦ stdSimplex.face {i, j}ᶜ) :=
    { iSup_eq := (boundary_eq_iSup N).symm
      eq_inf i j := by
        rw [stdSimplex.face_inter_face]
        congr 1
        ext k
        simp }
  (h.multicofork.toLinearOrder.map Subcomplex.toSSetFunctor).map F

@[simp]
theorem mappedBoundaryCocone_π (F : SSet.{u} ⥤ Type v) (N : ℕ)
    (i : Fin (N + 1)) :
    (mappedBoundaryCocone F N).π i = F.map (boundary.faceι i) := rfl

/-- Finite-colimit preservation gives the actual mapped boundary colimit. -/
def mappedBoundaryCoconeIsColimit (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (N : ℕ) : IsColimit (mappedBoundaryCocone F N) := by
  classical
  letI : Fintype (MultispanShape.ofLinearOrder (Fin (N + 1))).L :=
    inferInstanceAs (Fintype { p : Fin (N + 1) × Fin (N + 1) // p.1 < p.2 })
  letI : Fintype (MultispanShape.ofLinearOrder (Fin (N + 1))).R :=
    inferInstanceAs (Fintype (Fin (N + 1)))
  let h : Subcomplex.MulticoequalizerDiagram (boundary.{u} N)
      (fun i : Fin (N + 1) ↦ stdSimplex.face {i}ᶜ)
      (fun i j ↦ stdSimplex.face {i, j}ᶜ) :=
    { iSup_eq := (boundary_eq_iSup N).symm
      eq_inf i j := by
        rw [stdSimplex.face_inter_face]
        congr 1
        ext k
        simp }
  exact (h.multicofork.toLinearOrder.map Subcomplex.toSSetFunctor).isColimitMapOfPreserves
    F h.isColimit'

/-- Every mapped boundary point is the image of an original represented face. -/
theorem mappedBoundary_jointly_surjective (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (n : ℕ) (x : F.obj (∂Δ[n + 1] : SSet.{u})) :
    ∃ i : Fin (n + 2), ∃ a : F.obj (Δ[n] : SSet.{u}), F.map (boundary.ι i) a = x := by
  let d := (boundaryMultispan (n + 1)).map F
  let c := d.multispan.coconeTypesEquiv.symm (mappedBoundaryCocone F (n + 1))
  have hc : c.IsColimit := (Types.isColimit_iff_coconeTypesIsColimit _).1
    ⟨mappedBoundaryCoconeIsColimit F (n + 1)⟩
  obtain ⟨i, a, ha⟩ := ((Functor.CoconeTypes.isMulticoequalizer_iff c).1 hc).2 x
  change Fin (n + 2) at i
  change F.map (boundary.faceι i) a = x at ha
  refine ⟨i, F.map (stdSimplex.faceSingletonComplIso i).inv a, ?_⟩
  change (F.map (stdSimplex.faceSingletonComplIso i).inv ≫ F.map (boundary.ι i)) a = x
  rw [← F.map_comp, boundary.faceSingletonComplIso_inv_ι]
  exact ha

/-- The original represented coprojection followed by the original boundary inclusion. -/
@[reassoc]
theorem mappedBoundary_ι_comp (F : SSet.{u} ⥤ Type v) {n : ℕ} (i : Fin (n + 2)) :
    F.map (boundary.ι i) ≫ F.map ((boundary.{u} (n + 1)).ι) =
      F.map (stdSimplex.δ i) := by
  rw [← F.map_comp, boundary.ι_ι]

/-- The original represented cofaces into the mapped boundary. -/
def mappedBoundaryCofaceCocone (F : SSet.{u} ⥤ Type v) (n : ℕ) :
    Multicofork (SimplexCategory.cofaceMultispan (stdSimplex.{u} ⋙ F) n) :=
  Multicofork.ofπ _ (F.obj (∂Δ[n + 2] : SSet.{u}))
    (fun i ↦ F.map (boundary.ι i)) (fun p ↦ by
      have hij : p.1.1 < p.1.2 := p.2
      have w : stdSimplex.δ (p.1.2.pred (Fin.ne_zero_of_lt hij)) ≫ boundary.ι p.1.1 =
          stdSimplex.δ (p.1.1.castPred (Fin.ne_last_of_lt hij)) ≫ boundary.ι p.1.2 := by
        apply (cancel_mono ((boundary.{u} (n + 2)).ι)).1
        simp only [Category.assoc, boundary.ι_ι]
        exact (stdSimplex.facePairComplIso_hom_ι' p.1.1 p.1.2 hij).symm.trans
          (stdSimplex.facePairComplIso_hom_ι p.1.1 p.1.2 hij)
      change F.map (stdSimplex.δ (p.1.2.pred (Fin.ne_zero_of_lt hij))) ≫
          F.map (boundary.ι p.1.1) =
        F.map (stdSimplex.δ (p.1.1.castPred (Fin.ne_last_of_lt hij))) ≫
          F.map (boundary.ι p.1.2)
      rw [← F.map_comp, ← F.map_comp]
      exact F.congr_map w)

@[simp]
theorem mappedBoundaryCofaceCocone_π (F : SSet.{u} ⥤ Type v) (n : ℕ)
    (i : Fin (n + 3)) :
    (mappedBoundaryCofaceCocone F n).π i = F.map (boundary.ι i) := rfl

/-- Original face and doubleface isomorphisms identify the entire two diagrams. -/
def mappedBoundaryCofaceDiagramIso (F : SSet.{u} ⥤ Type v) (n : ℕ) :
    ((boundaryMultispan (n + 2)).map F).multispan ≅
      (SimplexCategory.cofaceMultispan (stdSimplex.{u} ⋙ F) n).multispan :=
  WalkingMultispan.functorExt
    (fun (p : { q : Fin (n + 3) × Fin (n + 3) // q.1 < q.2 }) ↦
      (F.mapIso (stdSimplex.facePairComplIso p.1.1 p.1.2 p.2)).symm)
    (fun (i : Fin (n + 3)) ↦ (F.mapIso (stdSimplex.faceSingletonComplIso i)).symm)
    (fun (p : { q : Fin (n + 3) × Fin (n + 3) // q.1 < q.2 }) ↦ by
      change F.map (Subcomplex.homOfLE (by simp [stdSimplex.face_le_face_iff])) ≫
          F.map (stdSimplex.faceSingletonComplIso p.1.1).inv =
        F.map (stdSimplex.facePairComplIso p.1.1 p.1.2 p.2).inv ≫
          F.map (stdSimplex.δ (p.1.2.pred (Fin.ne_zero_of_lt p.2)))
      rw [← F.map_comp, ← F.map_comp]
      exact F.congr_map
        (stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred
          p.1.1 p.1.2 p.2))
    (fun (p : { q : Fin (n + 3) × Fin (n + 3) // q.1 < q.2 }) ↦ by
      change F.map (Subcomplex.homOfLE (by simp [stdSimplex.face_le_face_iff])) ≫
          F.map (stdSimplex.faceSingletonComplIso p.1.2).inv =
        F.map (stdSimplex.facePairComplIso p.1.1 p.1.2 p.2).inv ≫
          F.map (stdSimplex.δ (p.1.1.castPred (Fin.ne_last_of_lt p.2)))
      rw [← F.map_comp, ← F.map_comp]
      exact F.congr_map
        (stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred
          p.1.1 p.1.2 p.2))

/-- The mapped boundary is a colimit of the original represented coface diagram. -/
def mappedBoundaryCofaceIsColimit (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (n : ℕ) : IsColimit (mappedBoundaryCofaceCocone F n) := by
  let e := mappedBoundaryCofaceDiagramIso F n
  let c := mappedBoundaryCofaceCocone F n
  apply (IsColimit.precomposeHomEquiv e c).toFun
  let ec : mappedBoundaryCocone F (n + 2) ≅ (Cocone.precompose e.hom).obj c :=
    Multicofork.ext (Iso.refl _) (fun (i : Fin (n + 3)) ↦ by
      change F.map (boundary.faceι i) ≫ 𝟙 _ =
        F.map (stdSimplex.faceSingletonComplIso i).inv ≫ F.map (boundary.ι i)
      rw [Category.comp_id, ← F.map_comp, boundary.faceSingletonComplIso_inv_ι])
  exact (mappedBoundaryCoconeIsColimit F (n + 2)).ofIsoColimit ec

/-- The actual mapped higher boundary is its literal union of original coface ranges. -/
def mappedBoundaryUnionIso (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F] (n : ℕ) :
    F.obj (∂Δ[n + 2] : SSet.{u}) ≅
      SimplexCategory.cofaceRangeUnion (stdSimplex.{u} ⋙ F) n :=
  (mappedBoundaryCofaceIsColimit F n).coconePointUniqueUpToIso
    (SimplexCategory.cofaceUnionIsColimit (stdSimplex.{u} ⋙ F) n)

@[reassoc]
theorem mappedBoundaryUnionIso_ι_hom (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (n : ℕ) (i : Fin (n + 3)) :
    F.map (boundary.ι i) ≫ (mappedBoundaryUnionIso F n).hom =
      (SimplexCategory.cofaceUnionCocone (stdSimplex.{u} ⋙ F) n).π i := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (mappedBoundaryCofaceIsColimit F n)
    (SimplexCategory.cofaceUnionIsColimit (stdSimplex.{u} ⋙ F) n) (WalkingMultispan.right i)

@[reassoc]
theorem mappedBoundaryUnionIso_ι_inv (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (n : ℕ) (i : Fin (n + 3)) :
    (SimplexCategory.cofaceUnionCocone (stdSimplex.{u} ⋙ F) n).π i ≫
        (mappedBoundaryUnionIso F n).inv = F.map (boundary.ι i) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_inv (mappedBoundaryCofaceIsColimit F n)
    (SimplexCategory.cofaceUnionIsColimit (stdSimplex.{u} ⋙ F) n) (WalkingMultispan.right i)

/-- The union isomorphism followed by its literal inclusion is the original mapped boundary map. -/
theorem mappedBoundaryUnionIso_hom_val (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (n : ℕ) :
    (mappedBoundaryUnionIso F n).hom ≫ (↾Subtype.val) =
      F.map ((boundary.{u} (n + 2)).ι) := by
  apply Multicofork.IsColimit.hom_ext (mappedBoundaryCofaceIsColimit F n)
  intro i
  change Fin (n + 3) at i
  change F.map (boundary.ι i) ≫ ((mappedBoundaryUnionIso F n).hom ≫ (↾Subtype.val)) =
    F.map (boundary.ι i) ≫ F.map ((boundary.{u} (n + 2)).ι)
  rw [← Category.assoc, mappedBoundaryUnionIso_ι_hom, mappedBoundary_ι_comp]
  ext a
  rfl

/-- The original mapped boundary inclusion is monic in every dimension at least two. -/
theorem mappedBoundaryComparison_isMono (F : SSet.{u} ⥤ Type v)
    [PreservesFiniteColimits F] (n : ℕ) : Mono (F.map ((boundary.{u} (n + 2)).ι)) := by
  let : Mono (↾Subtype.val :
      SimplexCategory.cofaceRangeUnion (stdSimplex.{u} ⋙ F) n ⟶
        F.obj (Δ[n + 2] : SSet.{u})) := (mono_iff_injective _).2 Subtype.val_injective
  rw [← mappedBoundaryUnionIso_hom_val F n]
  infer_instance

/-- The actual zero boundary remains initial. -/
def mappedBoundaryZeroIsInitial (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F] :
    IsInitial (F.obj (∂Δ[0] : SSet.{u})) := by
  simpa only [boundary_zero] using
    (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).isInitialObj F _

/-- The two original represented endpoint cofaces into the mapped one-boundary. -/
def mappedBoundaryOneCofan (F : SSet.{u} ⥤ Type v) :
    BinaryCofan (F.obj (Δ[0] : SSet.{u})) (F.obj (Δ[0] : SSet.{u})) :=
  BinaryCofan.mk (F.map (boundary.ι (0 : Fin 2))) (F.map (boundary.ι (1 : Fin 2)))

/-- The actual one-boundary is the coproduct of its two original represented endpoints. -/
def mappedBoundaryOneIsColimit (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F] :
    IsColimit (mappedBoundaryOneCofan F) := by
  let d := (boundaryMultispan 1).map F
  let hc := mappedBoundaryCoconeIsColimit F 1
  have leftInitial (p : { q : Fin 2 × Fin 2 // q.1 < q.2 }) :
      IsInitial (d.left p) := by
    have h : p.1.1.val < p.1.2.val := p.2
    have hi : p.1.1 = 0 := by
      apply Fin.ext
      have hj := p.1.2.is_lt
      omega
    have hj : p.1.2 = 1 := by
      apply Fin.ext
      have hj := p.1.2.is_lt
      simp only [hi, Fin.val_zero] at h
      omega
    change IsInitial (F.obj (stdSimplex.face {p.1.1, p.1.2}ᶜ : SSet.{u}))
    rw [hi, hj]
    have hp : ({(0 : Fin 2), 1}ᶜ : Finset (Fin 2)) = ∅ := by decide
    rw [hp, stdSimplex.face_empty]
    exact (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).isInitialObj F _
  let k (E : BinaryCofan (F.obj (Δ[0] : SSet.{u})) (F.obj (Δ[0] : SSet.{u})))
      (i : Fin 2) : F.obj (stdSimplex.face {i}ᶜ : SSet.{u}) ⟶ E.pt :=
    F.map (stdSimplex.faceSingletonComplIso i).inv ≫ if i = 0 then E.inl else E.inr
  have hk (E : BinaryCofan (F.obj (Δ[0] : SSet.{u})) (F.obj (Δ[0] : SSet.{u})))
      (p : { q : Fin 2 × Fin 2 // q.1 < q.2 }) :
      d.fst p ≫ k E p.1.1 = d.snd p ≫ k E p.1.2 :=
    (leftInitial p).hom_ext _ _
  let desc (E : BinaryCofan (F.obj (Δ[0] : SSet.{u})) (F.obj (Δ[0] : SSet.{u}))) :
      F.obj (∂Δ[1] : SSet.{u}) ⟶ E.pt := Multicofork.IsColimit.desc hc (k E) (hk E)
  have choices (i : Fin 2) : i = 0 ∨ i = 1 := by
    have hi := i.is_lt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  refine BinaryCofan.isColimitMk desc ?_ ?_ ?_
  · intro E
    apply (cancel_epi (F.map (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv)).1
    change F.map (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv ≫
        (F.map (boundary.ι (0 : Fin 2)) ≫ desc E) =
      F.map (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv ≫ E.inl
    rw [← Category.assoc, ← F.map_comp, boundary.faceSingletonComplIso_inv_ι]
    have hf := Multicofork.IsColimit.fac hc (k E) (hk E) (0 : Fin 2)
    change F.map (boundary.faceι (0 : Fin 2)) ≫ desc E = k E 0 at hf
    simpa only [k, ite_eq_left rfl, ite_true] using hf
  · intro E
    apply (cancel_epi (F.map (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv)).1
    change F.map (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫
        (F.map (boundary.ι (1 : Fin 2)) ≫ desc E) =
      F.map (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫ E.inr
    rw [← Category.assoc, ← F.map_comp, boundary.faceSingletonComplIso_inv_ι]
    have hf := Multicofork.IsColimit.fac hc (k E) (hk E) (1 : Fin 2)
    change F.map (boundary.faceι (1 : Fin 2)) ≫ desc E = k E 1 at hf
    simpa only [k, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), ite_false] using hf
  · intro E m h0 h1
    apply Multicofork.IsColimit.hom_ext hc
    intro i
    change Fin 2 at i
    have hm : F.map (boundary.faceι i) ≫ m = k E i := by
      rcases choices i with h | h
      · subst i
        change F.map (boundary.faceι (0 : Fin 2)) ≫ m =
          F.map (stdSimplex.faceSingletonComplIso (0 : Fin 2)).inv ≫ E.inl
        rw [← boundary.faceSingletonComplIso_inv_ι, F.map_comp, Category.assoc, h0]
      · subst i
        change F.map (boundary.faceι (1 : Fin 2)) ≫ m =
          F.map (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫ E.inr
        rw [← boundary.faceSingletonComplIso_inv_ι, F.map_comp, Category.assoc, h1]
    exact hm.trans (Multicofork.IsColimit.fac hc (k E) (hk E) i).symm

end SSet
