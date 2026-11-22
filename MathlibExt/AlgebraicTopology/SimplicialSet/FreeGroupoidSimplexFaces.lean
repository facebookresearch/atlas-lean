/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexCoordinates
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original full-J face pullbacks

An original full-J coface acts on every vertex by the original ordinal
coface. Compatibility with a standard simplex forces the unrestricted
source tuple to be monotone, giving the actual smaller standard simplex.
The resulting whole pullback retains both original maps and all pivots.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.FreeGroupoidSimplex

/-- The actual standard-simplex points are the compatible original full-J
and standard target points, with no monotonicity premise on the full-J tuple. -/
def simplexInclusionFacePointEquiv (n : ℕ) (i : Fin (n + 2)) (d : ℕ) :
    (Δ[n] : SSet.{u}).obj (op ⦋d⦌) ≃ Types.PullbackObj
      ((J.{u}.map (SimplexCategory.δ i)).app (op ⦋d⦌))
      ((simplexInclusion.{u}.app ⦋n + 1⦌).app (op ⦋d⦌)) where
  toFun s :=
    ⟨⟨(simplexInclusion.app ⦋n⦌).app (op ⦋d⦌) s,
      (stdSimplex.δ i).app (op ⦋d⦌) s⟩,
      congrArg (fun h => h.app (op ⦋d⦌) s)
        (simplexInclusion.naturality (SimplexCategory.δ i)).symm⟩
  invFun p := by
    let v := simplexVertexEquiv.{u} ⦋n⦌ d p.val.1
    have hv : Monotone v := by
      intro a b hab
      apply (Fin.succAboveOrderEmb i).le_iff_le.mp
      change i.succAbove (v a) ≤ i.succAbove (v b)
      have ha : i.succAbove (v a) = stdSimplex.asOrderHom p.val.2 a :=
        congrArg (fun x => (x.obj a).as.as.down) p.property
      have hb : i.succAbove (v b) = stdSimplex.asOrderHom p.val.2 b :=
        congrArg (fun x => (x.obj b).as.as.down) p.property
      rw [ha, hb]
      exact (stdSimplex.asOrderHom p.val.2).monotone hab
    exact ULift.up (SimplexCategory.mkHom ⟨v, hv⟩)
  left_inv s := by
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply (simplexVertexEquiv.{u} ⦋n⦌ d).injective
      funext k
      rfl
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext k
      exact congrArg (fun x => (x.obj k).as.as.down) p.property

/-- The first original forward leg of the point equivalence. -/
@[simp]
theorem simplexInclusionFacePointEquiv_fst (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (s : (Δ[n] : SSet.{u}).obj (op ⦋d⦌)) :
    (simplexInclusionFacePointEquiv.{u} n i d s).val.1 =
      (simplexInclusion.app ⦋n⦌).app (op ⦋d⦌) s := rfl

/-- The second original forward leg is the literal standard coface. -/
@[simp]
theorem simplexInclusionFacePointEquiv_snd (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (s : (Δ[n] : SSet.{u}).obj (op ⦋d⦌)) :
    (simplexInclusionFacePointEquiv.{u} n i d s).val.2 =
      (stdSimplex.δ i).app (op ⦋d⦌) s := rfl

/-- The inverse point has the original full-J source as its inclusion leg. -/
@[simp]
theorem simplexInclusionFacePointEquiv_symm_fst (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (p : Types.PullbackObj
      ((J.{u}.map (SimplexCategory.δ i)).app (op ⦋d⦌))
      ((simplexInclusion.{u}.app ⦋n + 1⦌).app (op ⦋d⦌))) :
    (simplexInclusion.app ⦋n⦌).app (op ⦋d⦌)
        ((simplexInclusionFacePointEquiv n i d).symm p) = p.val.1 :=
  congrArg (fun q => q.val.1)
    ((simplexInclusionFacePointEquiv n i d).apply_symm_apply p)

/-- The inverse point has the original target standard simplex as its coface leg. -/
@[simp]
theorem simplexInclusionFacePointEquiv_symm_snd (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (p : Types.PullbackObj
      ((J.{u}.map (SimplexCategory.δ i)).app (op ⦋d⦌))
      ((simplexInclusion.{u}.app ⦋n + 1⦌).app (op ⦋d⦌))) :
    (stdSimplex.δ i).app (op ⦋d⦌)
        ((simplexInclusionFacePointEquiv n i d).symm p) = p.val.2 :=
  congrArg (fun q => q.val.2)
    ((simplexInclusionFacePointEquiv n i d).apply_symm_apply p)

/-- The two original operators restrict the actual compatible pair. -/
def simplexInclusionFacePointMap (n : ℕ) (i : Fin (n + 2)) {d e : ℕ}
    (g : ⦋d⦌ ⟶ ⦋e⦌) :
    Types.PullbackObj
        ((J.{u}.map (SimplexCategory.δ i)).app (op ⦋e⦌))
        ((simplexInclusion.{u}.app ⦋n + 1⦌).app (op ⦋e⦌)) →
      Types.PullbackObj
        ((J.{u}.map (SimplexCategory.δ i)).app (op ⦋d⦌))
        ((simplexInclusion.{u}.app ⦋n + 1⦌).app (op ⦋d⦌)) :=
  fun p => ⟨⟨(J.obj ⦋n⦌).map g.op p.val.1,
      (Δ[n + 1] : SSet.{u}).map g.op p.val.2⟩, by
    calc
      _ = (J.obj ⦋n + 1⦌).map g.op
          ((J.map (SimplexCategory.δ i)).app (op ⦋e⦌) p.val.1) :=
        congrArg (fun h => h p.val.1) ((J.map (SimplexCategory.δ i)).naturality g.op)
      _ = (J.obj ⦋n + 1⦌).map g.op
          ((simplexInclusion.app ⦋n + 1⦌).app (op ⦋e⦌) p.val.2) :=
        congrArg ((J.obj ⦋n + 1⦌).map g.op) p.property
      _ = _ := (congrArg (fun h => h p.val.2)
        ((simplexInclusion.app ⦋n + 1⦌).naturality g.op)).symm⟩

/-- The whole forward point equivalence commutes with every original operator. -/
theorem simplexInclusionFacePointEquiv_operator (n : ℕ) (i : Fin (n + 2))
    {d e : ℕ} (g : ⦋d⦌ ⟶ ⦋e⦌)
    (s : (Δ[n] : SSet.{u}).obj (op ⦋e⦌)) :
    simplexInclusionFacePointEquiv.{u} n i d ((Δ[n] : SSet.{u}).map g.op s) =
      simplexInclusionFacePointMap n i g (simplexInclusionFacePointEquiv n i e s) := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun h => h s) ((simplexInclusion.app ⦋n⦌).naturality g.op)
  · exact congrArg (fun h => h s) ((stdSimplex.δ i).naturality g.op)

/-- The whole inverse point equivalence commutes with the same original operator. -/
theorem simplexInclusionFacePointEquiv_symm_operator (n : ℕ) (i : Fin (n + 2))
    {d e : ℕ} (g : ⦋d⦌ ⟶ ⦋e⦌)
    (p : Types.PullbackObj
      ((J.{u}.map (SimplexCategory.δ i)).app (op ⦋e⦌))
      ((simplexInclusion.{u}.app ⦋n + 1⦌).app (op ⦋e⦌))) :
    (Δ[n] : SSet.{u}).map g.op ((simplexInclusionFacePointEquiv n i e).symm p) =
      (simplexInclusionFacePointEquiv n i d).symm
        (simplexInclusionFacePointMap n i g p) := by
  apply (simplexInclusionFacePointEquiv n i d).injective
  rw [simplexInclusionFacePointEquiv_operator]
  simp only [Equiv.apply_symm_apply]

/-- Every original full-J coface is monic, proved from its actual vertex action. -/
instance J_coface_mono (n : ℕ) (i : Fin (n + 2)) :
    Mono (J.{u}.map (SimplexCategory.δ i)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro x y h
  apply (simplexVertexEquiv.{u} ⦋n⦌ d.unop.len).injective
  funext k
  have hv := congrArg (fun q => simplexVertexEquiv.{u} ⦋n + 1⦌ d.unop.len q k) h
  change i.succAbove (simplexVertexEquiv ⦋n⦌ d.unop.len x k) =
    i.succAbove (simplexVertexEquiv ⦋n⦌ d.unop.len y k) at hv
  exact (Fin.succAboveOrderEmb i).injective hv

/-- The original coface identifies all full-J source points with the target
tuples avoiding its pivot; the inverse permits repeated and reversed vertices. -/
def jCofaceRangeEquiv (n : ℕ) (i : Fin (n + 2)) (d : ℕ) :
    (J.{u}.obj ⦋n⦌).obj (op ⦋d⦌) ≃
      {x : (J.{u}.obj ⦋n + 1⦌).obj (op ⦋d⦌) //
        ∀ k, simplexVertexEquiv.{u} ⦋n + 1⦌ d x k ≠ i} where
  toFun y := ⟨(J.map (SimplexCategory.δ i)).app (op ⦋d⦌) y, by
    intro k
    change i.succAbove (simplexVertexEquiv.{u} ⦋n⦌ d y k) ≠ i
    exact Fin.succAbove_ne i _⟩
  invFun x :=
    (simplexVertexEquiv.{u} ⦋n⦌ d).symm (fun k =>
      (stdSimplex.finSuccAboveOrderIsoFinset i).symm
        ⟨simplexVertexEquiv.{u} ⦋n + 1⦌ d x.val k,
          by simpa only [Finset.mem_compl, Finset.mem_singleton] using x.property k⟩)
  left_inv y := by
    apply (simplexVertexEquiv.{u} ⦋n⦌ d).injective
    funext k
    simp only [Equiv.apply_symm_apply]
    exact (stdSimplex.finSuccAboveOrderIsoFinset i).symm_apply_apply
      (simplexVertexEquiv.{u} ⦋n⦌ d y k)
  right_inv x := by
    apply Subtype.ext
    apply (simplexVertexEquiv.{u} ⦋n + 1⦌ d).injective
    funext k
    rw [simplexVertexEquiv_site, Equiv.apply_symm_apply]
    exact congrArg (fun q => q.val)
      ((stdSimplex.finSuccAboveOrderIsoFinset i).apply_symm_apply _)

/-- The range equivalence uses the literal original coface map. -/
theorem jCofaceRangeEquiv_apply (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (y : (J.{u}.obj ⦋n⦌).obj (op ⦋d⦌)) :
    (jCofaceRangeEquiv.{u} n i d y).val =
      (J.map (SimplexCategory.δ i)).app (op ⦋d⦌) y := rfl

/-- The actual inverse removes the pivot by the native complement order isomorphism. -/
theorem jCofaceRangeEquiv_symm_vertex (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (x : {x : (J.{u}.obj ⦋n + 1⦌).obj (op ⦋d⦌) //
      ∀ k, simplexVertexEquiv.{u} ⦋n + 1⦌ d x k ≠ i}) (k : Fin (d + 1)) :
    simplexVertexEquiv.{u} ⦋n⦌ d ((jCofaceRangeEquiv n i d).symm x) k =
      (stdSimplex.finSuccAboveOrderIsoFinset i).symm
        ⟨simplexVertexEquiv.{u} ⦋n + 1⦌ d x.val k,
          by simpa only [Finset.mem_compl, Finset.mem_singleton] using x.property k⟩ := by
  exact congrFun ((simplexVertexEquiv.{u} ⦋n⦌ d).apply_symm_apply _) k

/-- The same inverse returns a preimage of the original target full-J point. -/
theorem jCofaceRangeEquiv_symm_map (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (x : {x : (J.{u}.obj ⦋n + 1⦌).obj (op ⦋d⦌) //
      ∀ k, simplexVertexEquiv.{u} ⦋n + 1⦌ d x k ≠ i}) :
    (J.map (SimplexCategory.δ i)).app (op ⦋d⦌)
        ((jCofaceRangeEquiv.{u} n i d).symm x) = x.val :=
  congrArg (fun q => q.val) ((jCofaceRangeEquiv.{u} n i d).apply_symm_apply x)

/-- In every degree, the original coface image is exactly the tuples avoiding its pivot. -/
theorem J_coface_range_iff (n : ℕ) (i : Fin (n + 2)) (d : ℕ)
    (x : (J.{u}.obj ⦋n + 1⦌).obj (op ⦋d⦌)) :
    x ∈ (Subcomplex.range (J.map (SimplexCategory.δ i))).obj (op ⦋d⦌) ↔
      ∀ k, simplexVertexEquiv ⦋n + 1⦌ d x k ≠ i := by
  change (∃ y, (J.map (SimplexCategory.δ i)).app (op ⦋d⦌) y = x) ↔ _
  constructor
  · rintro ⟨y, rfl⟩ k
    change i.succAbove (simplexVertexEquiv ⦋n⦌ d y k) ≠ i
    exact Fin.succAbove_ne i _
  · intro hx
    exact ⟨(jCofaceRangeEquiv.{u} n i d).symm ⟨x, hx⟩,
      jCofaceRangeEquiv_symm_map n i d ⟨x, hx⟩⟩

/-- The original coface and both original inclusions form an actual whole pullback. -/
theorem simplexInclusion_face_isPullback (n : ℕ) (i : Fin (n + 2)) :
    IsPullback (simplexInclusion.{u}.app ⦋n⦌) (stdSimplex.{u}.δ i)
      (J.{u}.map (SimplexCategory.δ i)) (simplexInclusion.{u}.app ⦋n + 1⦌) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun h => h.app d)
      (simplexInclusion.naturality (SimplexCategory.δ i)).symm
  · intro x y h
    apply (simplexInclusionFacePointEquiv.{u} n i d.unop.len).injective
    apply Subtype.ext
    exact Prod.ext h.1 h.2
  · intro x y h
    let p : Types.PullbackObj
        ((J.{u}.map (SimplexCategory.δ i)).app d)
        ((simplexInclusion.{u}.app ⦋n + 1⦌).app d) := ⟨⟨x, y⟩, h⟩
    exact ⟨(simplexInclusionFacePointEquiv n i d.unop.len).symm p,
      simplexInclusionFacePointEquiv_symm_fst n i d.unop.len p,
      simplexInclusionFacePointEquiv_symm_snd n i d.unop.len p⟩

/-- Pulling the original full-J coface image back gives the literal standard face. -/
theorem simplexInclusion_face_preimage (n : ℕ) (i : Fin (n + 2)) :
    (Subcomplex.range (J.{u}.map (SimplexCategory.δ i))).preimage
        (simplexInclusion.{u}.app ⦋n + 1⦌) = stdSimplex.face {i}ᶜ := by
  ext d s
  change ((simplexInclusion.app ⦋n + 1⦌).app d s ∈
    (Subcomplex.range (J.map (SimplexCategory.δ i))).obj d) ↔ _
  rw [J_coface_range_iff n i d.unop.len]
  change (∀ k : Fin (d.unop.len + 1), stdSimplex.asOrderHom s k ≠ i) ↔
    Finset.image (stdSimplex.asOrderHom s) Finset.univ ≤ {i}ᶜ
  constructor
  · intro h z hz
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    simpa only [Finset.mem_compl, Finset.mem_singleton] using h k
  · intro h k
    have hz := h (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    simpa only [Finset.mem_compl, Finset.mem_singleton] using hz

/-- The actual empty standard boundary uses the original zero inclusion isomorphism. -/
theorem simplexInclusion_zero_emptyBoundary_isPullback :
    IsPullback (𝟙 (SSet.boundary.{u} 0 : SSet.{u})) (SSet.boundary 0).ι
      ((SSet.boundary 0).ι ≫ simplexInclusion.app ⦋0⦌)
      (simplexInclusion.{u}.app ⦋0⦌) := by
  apply IsPullback.of_horiz_isIso
  exact ⟨by simp only [Category.id_comp]⟩

end SSet.FreeGroupoidSimplex
