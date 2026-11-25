/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.LastVertex
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Nonsingular
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Data.Finset.Sort
import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda

/-!
# Anchored normal forms for subdivision simplices

This file gives the degreewise normal form of a simplex in the Kan
subdivision of an arbitrary simplicial set.  A normal form consists of one
nondegenerate carrier and a weak flag of nonempty faces in its standard
simplex whose terminal face is full.

The construction retains repeated faces and repeated carrier values.  It
does not assume nonsingularity and does not state subdivision regularity, a
Barratt factorization, or a realization theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

private theorem sdMap_apply_heq {m n m' n' d : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋m'⦌ ⟶ ⦋n'⦌)
    (F : (SimplexCategory.sd.{u}.obj ⦋m⦌) _⦋d⦌)
    (G : (SimplexCategory.sd.{u}.obj ⦋m'⦌) _⦋d⦌)
    (hm : m = m') (hn : n = n') (hf : HEq f g) (hF : HEq F G) :
    HEq ((SimplexCategory.sd.map f).app _ F)
      ((SimplexCategory.sd.map g).app _ G) := by
  cases hm
  cases hn
  apply heq_of_eq
  rw [eq_of_heq hf, eq_of_heq hF]

/-- The full nonempty face of a finite ordinal. -/
def sdFullFace (n : SimplexCategory) :
    PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) where
  finset := Finset.univ
  comparable _ _ := le_total _ _

@[simp]
theorem mem_sdFullFace (n : SimplexCategory)
    (i : ULift.{u} (Fin (n.len + 1))) : i ∈ (sdFullFace n).finset := by
  simp [sdFullFace]

/-- The top nondegenerate simplex of the standard simplex in a carrier's
dimension. -/
def sdTopCarrier {X : SSet.{u}} (a : X.N) :
    (Δ[a.dim] : SSet.{u}).N :=
  SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋a.dim⦌))
    (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate a.dim)

private noncomputable def anchoredFaceOfLE {Y : SSet.{u}}
    [Y.Nonsingular] {x a : Y.N} (h : x ≤ a) :
    (Δ[a.dim] : SSet.{u}).N := by
  let f := SSet.N.monoOfLE h
  have hf : Mono f := by dsimp [f]; infer_instance
  exact SSet.N.mk (SSet.stdSimplex.objEquiv.symm f)
    ((SSet.stdSimplex.mem_nonDegenerate_iff_mono _).2 (by
      change Mono f
      exact hf))

private theorem anchoredMap_faceOfLE {Y : SSet.{u}} [Y.Nonsingular]
    {x a : Y.N} (h : x ≤ a) :
    SSet.N.map (SSet.yonedaEquiv.symm a.simplex)
      (anchoredFaceOfLE h) = x := by
  let f := SSet.N.monoOfLE h
  have himage :
      (SSet.yonedaEquiv.symm a.simplex).app _
          (SSet.stdSimplex.objEquiv.symm f) = x.simplex := by
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact SSet.N.map_monoOfLE h
  have hnon :
      (SSet.yonedaEquiv.symm a.simplex).app _
          (anchoredFaceOfLE h).simplex ∈
        Y.nonDegenerate (anchoredFaceOfLE h).dim := by
    change (SSet.yonedaEquiv.symm a.simplex).app _
      (SSet.stdSimplex.objEquiv.symm f) ∈ Y.nonDegenerate x.dim
    rw [himage]
    exact x.nonDegenerate
  rw [SSet.N.map_eq_mk _ _ hnon, SSet.N.ext_iff]
  change SSet.S.mk
      ((SSet.yonedaEquiv.symm a.simplex).app _
        (SSet.stdSimplex.objEquiv.symm f)) = x.toS
  rw [himage]

private theorem anchoredN_map_le_iff_of_mono {Y Z : SSet.{u}}
    (f : Y ⟶ Z) [Mono f] (x y : Y.N) :
    SSet.N.map f x ≤ SSet.N.map f y ↔ x ≤ y := by
  rw [SSet.N.le_iff, SSet.N.le_iff,
    SSet.N.map_subcomplex, SSet.N.map_subcomplex,
    SSet.Subcomplex.image_le_image_iff]

private theorem anchoredN_map_injective_of_mono {Y Z : SSet.{u}}
    (f : Y ⟶ Z) [Mono f] : Function.Injective (SSet.N.map f) := by
  intro x y h
  apply le_antisymm
  · exact (anchoredN_map_le_iff_of_mono f x y).mp h.le
  · exact (anchoredN_map_le_iff_of_mono f y x).mp h.ge

private theorem anchoredNerve_map_injective_of_mono {Y Z : SSet.{u}}
    (f : Y ⟶ Z) [Mono f] {d : ℕ} :
    Function.Injective
      ((SSet.nondegenerateNerve.map f).app (op ⦋d⦌)) := by
  intro c c' h
  apply ComposableArrows.ext
    (h := fun j => anchoredN_map_injective_of_mono f
      (congrArg (fun z => z.obj j) h))
    (w := by
      intro i hi
      subsingleton)

private theorem map_eqToHom_dim_apply {X : SSet.{u}} {m n : ℕ}
    (h : m = n) (x : X _⦋m⦌) :
    X.map (CategoryTheory.eqToHom
      (congrArg (fun k : ℕ => ⦋k⦌) h).symm).op x =
      cast (congrArg (fun k : ℕ => X _⦋k⦌) h) x := by
  cases h
  simp

private theorem stdSimplex_objEquiv_map_apply
    {l m n : SimplexCategory} (f : m ⟶ n)
    (x : (SSet.stdSimplex.{u}.obj m).obj (op l)) :
    SSet.stdSimplex.objEquiv
        ((SSet.stdSimplex.map f).app _ x) =
      SSet.stdSimplex.objEquiv x ≫ f := by
  rfl

private theorem nondegenerate_toNπ_heq_id {X : SSet.{u}} (a : X.N) :
    HEq a.toS.toNπ (𝟙 ⦋a.dim⦌) := by
  have hN : a.toS.toN = a :=
    (SSet.S.toN_eq_iff).2 rfl
  have hdim : a.toS.toN.dim = a.dim :=
    congrArg (fun z : X.N => z.dim) hN
  have hsimp : HEq a.toS.toN.simplex a.simplex :=
    congr_arg_heq (fun z : X.N => z.simplex) hN
  have hObj : ⦋a.toS.toN.dim⦌ = ⦋a.dim⦌ :=
    congrArg (fun n : ℕ => ⦋n⦌) hdim
  have hType : X _⦋a.toS.toN.dim⦌ = X _⦋a.dim⦌ :=
    congrArg (fun n : ℕ => X _⦋n⦌) hdim
  have hcast : cast hType a.toS.toN.simplex = a.simplex :=
    eq_of_heq ((cast_heq_iff_heq hType _ _).2 hsimp)
  apply (CategoryTheory.conj_eqToHom_iff_heq
    a.toS.toNπ (𝟙 ⦋a.dim⦌) rfl hObj).mp
  simp only [CategoryTheory.eqToHom_refl, Category.id_comp]
  apply X.unique_nonDegenerate_map a.simplex a.toS.toNπ
    ⟨a.toS.toN.simplex, a.toS.toN.nonDegenerate⟩
    (SSet.S.map_toNπ_op_apply a.toS).symm
    (CategoryTheory.eqToHom hObj.symm)
    ⟨a.toS.toN.simplex, a.toS.toN.nonDegenerate⟩
  rw [map_eqToHom_dim_apply hdim]
  exact hcast.symm

private noncomputable def anchoredLiftCarrierChain {Y : SSet.{u}}
    [Y.Nonsingular] {d : ℕ} (c : (CategoryTheory.nerve Y.N) _⦋d⦌) :
    (CategoryTheory.nerve
      (Δ[(c.obj (Fin.last d)).dim] : SSet.{u}).N) _⦋d⦌ :=
  (show Fin (d + 1) →o
      (Δ[(c.obj (Fin.last d)).dim] : SSet.{u}).N from
    { toFun := fun j => anchoredFaceOfLE (c.monotone (Fin.le_last j))
      monotone' := fun i j hij => by
        let y := SSet.yonedaEquiv.symm
          (c.obj (Fin.last d)).simplex
        let _ : Mono y := SSet.Nonsingular.mono'
          (c.obj (Fin.last d)).simplex
          (c.obj (Fin.last d)).nonDegenerate
        rw [← anchoredN_map_le_iff_of_mono y]
        rw [anchoredMap_faceOfLE, anchoredMap_faceOfLE]
        exact c.monotone hij }).monotone.functor

private theorem anchoredLiftCarrierChain_last {Y : SSet.{u}}
    [Y.Nonsingular] {d : ℕ} (c : (CategoryTheory.nerve Y.N) _⦋d⦌) :
    (anchoredLiftCarrierChain c).obj (Fin.last d) =
      sdTopCarrier (c.obj (Fin.last d)) := by
  change anchoredFaceOfLE
      (c.monotone (Fin.le_last (Fin.last d))) = _
  apply SSet.N.subcomplex_injective
  change SSet.Subcomplex.ofSimplex
      (SSet.stdSimplex.objEquiv.symm
        (SSet.N.monoOfLE (c.monotone (Fin.le_last (Fin.last d))))) =
    SSet.Subcomplex.ofSimplex
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋(c.obj (Fin.last d)).dim⦌))
  congr 2
  exact SSet.N.monoOfLE_refl (c.obj (Fin.last d))

private theorem anchoredMap_liftCarrierChain {Y : SSet.{u}}
    [Y.Nonsingular] {d : ℕ} (c : (CategoryTheory.nerve Y.N) _⦋d⦌) :
    (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm (c.obj (Fin.last d)).simplex)).app _
        (anchoredLiftCarrierChain c) = c := by
  apply ComposableArrows.ext
    (h := fun j => by
      change SSet.N.map
        (SSet.yonedaEquiv.symm (c.obj (Fin.last d)).simplex)
        (anchoredFaceOfLE (c.monotone (Fin.le_last j))) = c.obj j
      exact anchoredMap_faceOfLE _)
    (w := by
      intro i hi
      subsingleton)

private theorem anchoredMap_liftCarrierChain_of_last_eq {Y : SSet.{u}}
    [Y.Nonsingular] {d : ℕ} (c : (CategoryTheory.nerve Y.N) _⦋d⦌)
    (t : Y.N) (h : c.obj (Fin.last d) = t) :
    (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm t.simplex)).app _
        (cast (congrArg (fun z : Y.N =>
          (CategoryTheory.nerve
            (Δ[z.dim] : SSet.{u}).N) _⦋d⦌) h)
          (anchoredLiftCarrierChain c)) = c := by
  cases h
  refine (congrArg
    (fun q => (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm (c.obj (Fin.last d)).simplex)).app _ q)
    (eq_of_heq (cast_heq _ (anchoredLiftCarrierChain c)))).trans ?_
  exact anchoredMap_liftCarrierChain c

private theorem anchoredMap_topCarrier_epi {m n : SimplexCategory}
    (f : m ⟶ n) [Epi f] :
    SSet.N.map (SSet.stdSimplex.map f)
      (SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 m))
        (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate m.len)) =
      SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 n))
        (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate n.len) := by
  let _ := isSplitEpi_of_epi f
  let _ : Epi (SSet.stdSimplex.map f) := inferInstance
  apply SSet.N.subcomplex_injective
  rw [SSet.N.map_subcomplex]
  change (SSet.Subcomplex.ofSimplex
      (SSet.stdSimplex.objEquiv.symm (𝟙 m))).image
      (SSet.stdSimplex.map f) =
    SSet.Subcomplex.ofSimplex
      (SSet.stdSimplex.objEquiv.symm (𝟙 n))
  rw [SSet.stdSimplex.ofSimplex_objEquiv_symm_id,
    SSet.stdSimplex.ofSimplex_objEquiv_symm_id,
    SSet.Subcomplex.image_top]
  apply SSet.Subcomplex.range_eq_top

/-- Carrier chain of a representable subdivision flag. -/
noncomputable def sdFlagCarrierChain (n : SimplexCategory) {d : ℕ}
    (F : (SimplexCategory.sd.{u}.obj n) _⦋d⦌) :
    (CategoryTheory.nerve (Δ[n.len] : SSet.{u}).N) _⦋d⦌ :=
  (SSet.sdToNondegenerateNerve.app (Δ[n.len] : SSet.{u})).app _
    ((SSet.stdSimplex.sdIso.inv.app n).app _ F)

/-- Representable subdivision flag corresponding to a chain of
nondegenerate faces. -/
noncomputable def sdFlagOfCarrierChain (n : SimplexCategory) {d : ℕ}
    (c : (CategoryTheory.nerve
      (Δ[n.len] : SSet.{u}).N) _⦋d⦌) :
    (SimplexCategory.sd.{u}.obj n) _⦋d⦌ :=
  (SSet.stdSimplex.sdIso.hom.app n).app _
    ((SSet.sdIsoNondegenerateNerve
      (Δ[n.len] : SSet.{u})).inv.app _ c)

private theorem sdFlagOfCarrierChain_heq {m n d : ℕ}
    (c : (CategoryTheory.nerve (Δ[m] : SSet.{u}).N) _⦋d⦌)
    (c' : (CategoryTheory.nerve (Δ[n] : SSet.{u}).N) _⦋d⦌)
    (hmn : m = n) (hcc : HEq c c') :
    HEq (sdFlagOfCarrierChain ⦋m⦌ c)
      (sdFlagOfCarrierChain ⦋n⦌ c') := by
  cases hmn
  apply heq_of_eq
  rw [eq_of_heq hcc]

private theorem sdFlagLift_of_last_eq {Y : SSet.{u}}
    [Y.Nonsingular] {d : ℕ} (c : (CategoryTheory.nerve Y.N) _⦋d⦌)
    (t : Y.N) (h : c.obj (Fin.last d) = t) :
    HEq
      (sdFlagOfCarrierChain ⦋(c.obj (Fin.last d)).dim⦌
        (anchoredLiftCarrierChain c))
      (sdFlagOfCarrierChain ⦋t.dim⦌
        (cast (congrArg (fun z : Y.N =>
          (CategoryTheory.nerve
            (Δ[z.dim] : SSet.{u}).N) _⦋d⦌) h)
          (anchoredLiftCarrierChain c))) := by
  cases h
  apply heq_of_eq
  exact congrArg (sdFlagOfCarrierChain ⦋(c.obj (Fin.last d)).dim⦌)
    (eq_of_heq (cast_heq _ (anchoredLiftCarrierChain c))).symm

@[simp]
theorem sdFlagCarrierChain_flagOfCarrierChain
    (n : SimplexCategory) {d : ℕ}
    (c : (CategoryTheory.nerve
      (Δ[n.len] : SSet.{u}).N) _⦋d⦌) :
    sdFlagCarrierChain n (sdFlagOfCarrierChain n c) = c := by
  unfold sdFlagCarrierChain sdFlagOfCarrierChain
  let w := (SSet.sdIsoNondegenerateNerve
    (Δ[n.len] : SSet.{u})).inv.app _ c
  have hsd : (SSet.stdSimplex.sdIso.inv.app n).app _
      ((SSet.stdSimplex.sdIso.hom.app n).app _ w) = w := by
    change ((SSet.stdSimplex.sdIso.hom.app n ≫
      SSet.stdSimplex.sdIso.inv.app n).app (op ⦋d⦌)) w = w
    rw [Iso.hom_inv_id_app]
    rfl
  change (SSet.sdToNondegenerateNerve.app
      (Δ[n.len] : SSet.{u})).app _
      ((SSet.stdSimplex.sdIso.inv.app n).app _
        ((SSet.stdSimplex.sdIso.hom.app n).app _ w)) = c
  rw [hsd, ← SSet.sdIsoNondegenerateNerve_hom]
  let c' : (SSet.nondegenerateNerve.obj
      (Δ[n.len] : SSet.{u})) _⦋d⦌ := c
  change ((SSet.sdIsoNondegenerateNerve
    (Δ[n.len] : SSet.{u})).inv ≫
      (SSet.sdIsoNondegenerateNerve
        (Δ[n.len] : SSet.{u})).hom).app _ c' = c'
  exact ConcreteCategory.congr_hom
    (Iso.inv_hom_id_app
      (SSet.sdIsoNondegenerateNerve (Δ[n.len] : SSet.{u})) _) c'

@[simp]
theorem sdFlagOfCarrierChain_flagCarrierChain
    (n : SimplexCategory) {d : ℕ}
    (F : (SimplexCategory.sd.{u}.obj n) _⦋d⦌) :
    sdFlagOfCarrierChain n (sdFlagCarrierChain n F) = F := by
  unfold sdFlagCarrierChain sdFlagOfCarrierChain
  let v := (SSet.stdSimplex.sdIso.inv.app n).app _ F
  have hN : (SSet.sdIsoNondegenerateNerve
      (Δ[n.len] : SSet.{u})).inv.app _
      ((SSet.sdIsoNondegenerateNerve
        (Δ[n.len] : SSet.{u})).hom.app _ v) = v := by
    exact ConcreteCategory.congr_hom
      (Iso.hom_inv_id_app
        (SSet.sdIsoNondegenerateNerve (Δ[n.len] : SSet.{u})) _) v
  have hsd : (SSet.stdSimplex.sdIso.hom.app n).app _
      ((SSet.stdSimplex.sdIso.inv.app n).app _ F) = F := by
    change ((SSet.stdSimplex.sdIso.inv.app n ≫
      SSet.stdSimplex.sdIso.hom.app n).app (op ⦋d⦌)) F = F
    rw [Iso.inv_hom_id_app]
    rfl
  change (SSet.stdSimplex.sdIso.hom.app n).app _
      ((SSet.sdIsoNondegenerateNerve
        (Δ[n.len] : SSet.{u})).inv.app _
        ((SSet.sdToNondegenerateNerve.app
          (Δ[n.len] : SSet.{u})).app _ v)) = F
  rw [← SSet.sdIsoNondegenerateNerve_hom, hN]
  exact hsd

/-- Carrier chains of representable flags are natural for every simplex
operator, including non-monic degeneracies. -/
theorem sdFlagCarrierChain_map {m n : SimplexCategory} (f : m ⟶ n)
    {d : ℕ} (F : (SimplexCategory.sd.{u}.obj m) _⦋d⦌) :
    sdFlagCarrierChain n ((SimplexCategory.sd.map f).app _ F) =
      (SSet.nondegenerateNerve.map (SSet.stdSimplex.map f)).app _
        (sdFlagCarrierChain m F) := by
  unfold sdFlagCarrierChain
  have hIso := SSet.stdSimplex.sdIso.inv.naturality f
  have hComp := SSet.sdToNondegenerateNerve.naturality
    (SSet.stdSimplex.map f)
  have hIso' := congrArg
    (fun g => g.app (op ⦋d⦌) F) hIso
  have hComp' := congrArg
    (fun g => g.app (op ⦋d⦌)
      ((SSet.stdSimplex.sdIso.inv.app m).app _ F)) hComp
  change (SSet.stdSimplex.sdIso.inv.app n).app _
      ((SimplexCategory.sd.map f).app _ F) =
    (SSet.sd.map (SSet.stdSimplex.map f)).app _
      ((SSet.stdSimplex.sdIso.inv.app m).app _ F) at hIso'
  change (SSet.sdToNondegenerateNerve.app
      (SSet.stdSimplex.obj n)).app _
      ((SSet.sd.map (SSet.stdSimplex.map f)).app _
        ((SSet.stdSimplex.sdIso.inv.app m).app _ F)) =
    (SSet.nondegenerateNerve.map (SSet.stdSimplex.map f)).app _
      ((SSet.sdToNondegenerateNerve.app
        (SSet.stdSimplex.obj m)).app _
          ((SSet.stdSimplex.sdIso.inv.app m).app _ F)) at hComp'
  change (SSet.sdToNondegenerateNerve.app (Δ[n.len] : SSet.{u})).app _
      ((SSet.stdSimplex.sdIso.inv.app n).app _
        ((SimplexCategory.sd.map f).app _ F)) = _
  rw [hIso']
  exact hComp'

/-- Carrier chains commute with simplicial operators in the flag degree. -/
theorem sdFlagCarrierChain_obj_map (n : SimplexCategory)
    {d e : ℕ} (f : ⦋e⦌ ⟶ ⦋d⦌)
    (F : (SimplexCategory.sd.{u}.obj n) _⦋d⦌) :
    sdFlagCarrierChain n
        ((SimplexCategory.sd.obj n).map f.op F) =
      (SSet.nondegenerateNerve.obj
        (Δ[n.len] : SSet.{u})).map f.op
          (sdFlagCarrierChain n F) := by
  unfold sdFlagCarrierChain
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]

/-- Reconstruction of representable flags from carrier chains is natural for
arbitrary simplex operators. -/
theorem sdFlagOfCarrierChain_map {m n : SimplexCategory} (f : m ⟶ n)
    {d : ℕ}
    (c : (CategoryTheory.nerve
      (Δ[m.len] : SSet.{u}).N) _⦋d⦌) :
    (SimplexCategory.sd.map f).app _ (sdFlagOfCarrierChain m c) =
      sdFlagOfCarrierChain n
        ((SSet.nondegenerateNerve.map (SSet.stdSimplex.map f)).app _ c) := by
  have hinj : Function.Injective (sdFlagCarrierChain n (d := d)) := by
    intro F G h
    rw [← sdFlagOfCarrierChain_flagCarrierChain n F,
      ← sdFlagOfCarrierChain_flagCarrierChain n G, h]
  apply hinj
  rw [sdFlagCarrierChain_map,
    sdFlagCarrierChain_flagOfCarrierChain]
  exact (sdFlagCarrierChain_flagOfCarrierChain n _).symm

/-- A weak subdivision flag in a nondegenerate carrier, anchored by the full
terminal face. -/
@[ext]
structure SdAnchoredFlag (X : SSet.{u}) (d : ℕ) where
  carrier : X.N
  flag : (SimplexCategory.sd.{u}.obj ⦋carrier.dim⦌) _⦋d⦌
  terminal_full :
    (sdFlagCarrierChain ⦋carrier.dim⦌ flag).obj (Fin.last d) =
      sdTopCarrier carrier

namespace SdAnchoredFlag

variable {X : SSet.{u}} {d : ℕ}

/-- The subdivision simplex represented by an anchored flag. -/
def toSimplex (a : SdAnchoredFlag X d) : (SSet.sd.obj X) _⦋d⦌ :=
  (SSet.sd.map (SSet.yonedaEquiv.symm a.carrier.simplex)).app _
    ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag)

/-- The terminal face of an anchored flag is full. -/
@[simp]
theorem flag_last (a : SdAnchoredFlag X d) :
    (sdFlagCarrierChain ⦋a.carrier.dim⦌ a.flag).obj (Fin.last d) =
      sdTopCarrier a.carrier :=
  a.terminal_full

end SdAnchoredFlag

@[no_expose] noncomputable abbrev normalizedTerminalSimplex {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) : X.S :=
  SSet.S.mk ((SSet.yonedaEquiv.symm x.simplex).app _
    ((sdFlagCarrierChain ⦋x.dim⦌ F).obj (Fin.last d)).simplex)

@[no_expose] noncomputable abbrev normalizedCarrier {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) : X.N :=
  (normalizedTerminalSimplex x F).toN

@[no_expose] noncomputable def normalizedFlag {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) :
    (SimplexCategory.sd.{u}.obj
      ⦋(normalizedCarrier x F).dim⦌) _⦋d⦌ :=
  (SimplexCategory.sd.map (normalizedTerminalSimplex x F).toNπ).app _
    (sdFlagOfCarrierChain
      ⦋((sdFlagCarrierChain ⦋x.dim⦌ F).obj (Fin.last d)).dim⦌
      (anchoredLiftCarrierChain (sdFlagCarrierChain ⦋x.dim⦌ F)))

theorem normalizedFlag_terminal {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) :
    (sdFlagCarrierChain ⦋(normalizedCarrier x F).dim⦌
      (normalizedFlag x F)).obj (Fin.last d) =
        sdTopCarrier (normalizedCarrier x F) := by
  let c := sdFlagCarrierChain ⦋x.dim⦌ F
  let t := c.obj (Fin.last d)
  let s := normalizedTerminalSimplex x F
  let b := normalizedCarrier x F
  let π := s.toNπ
  change (sdFlagCarrierChain ⦋b.dim⦌
    ((SimplexCategory.sd.map π).app _
      (sdFlagOfCarrierChain ⦋t.dim⦌
        (anchoredLiftCarrierChain c)))).obj (Fin.last d) = _
  rw [sdFlagCarrierChain_map]
  change SSet.N.map (SSet.stdSimplex.map π)
      ((sdFlagCarrierChain ⦋t.dim⦌
        (sdFlagOfCarrierChain ⦋t.dim⦌
          (anchoredLiftCarrierChain c))).obj (Fin.last d)) = _
  rw [sdFlagCarrierChain_flagOfCarrierChain,
    anchoredLiftCarrierChain_last]
  change SSet.N.map (SSet.stdSimplex.map π)
      (SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋t.dim⦌))
        (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate t.dim)) =
    SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋b.dim⦌))
      (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate b.dim)
  exact anchoredMap_topCarrier_epi π

/-- Normalization of one standard-simplex representative. -/
noncomputable def sdNormalizeRepresentative {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) :
    SdAnchoredFlag X d where
  carrier := normalizedCarrier x F
  flag := normalizedFlag x F
  terminal_full := normalizedFlag_terminal x F

theorem sdNormalizeRepresentative_toSimplex {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) :
    (sdNormalizeRepresentative x F).toSimplex =
      (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _
        ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ F) := by
  let c := sdFlagCarrierChain ⦋x.dim⦌ F
  let t := c.obj (Fin.last d)
  let s := normalizedTerminalSimplex x F
  let b := normalizedCarrier x F
  let π := s.toNπ
  let μ := SSet.stdSimplex.objEquiv t.simplex
  let L := anchoredLiftCarrierChain c
  let Ft := sdFlagOfCarrierChain ⦋t.dim⦌ L
  let v := (SSet.stdSimplex.sdIso.inv.app ⦋t.dim⦌).app _ Ft
  have htchar : SSet.stdSimplex.map μ =
      SSet.yonedaEquiv.symm t.simplex := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_map, Equiv.apply_symm_apply]
    exact SSet.stdSimplex.objEquiv.symm_apply_apply t.simplex
  have hflag : (SimplexCategory.sd.map μ).app _ Ft = F := by
    calc
      (SimplexCategory.sd.map μ).app _ Ft =
          sdFlagOfCarrierChain ⦋x.dim⦌
            ((SSet.nondegenerateNerve.map
              (SSet.stdSimplex.map μ)).app _ L) :=
        sdFlagOfCarrierChain_map μ L
      _ = sdFlagOfCarrierChain ⦋x.dim⦌ c := by
        rw [htchar, anchoredMap_liftCarrierChain]
      _ = F := sdFlagOfCarrierChain_flagCarrierChain ⦋x.dim⦌ F
  have hchar : SSet.stdSimplex.map π ≫
        SSet.yonedaEquiv.symm b.simplex =
      SSet.stdSimplex.map μ ≫
        SSet.yonedaEquiv.symm x.simplex := by
    rw [SSet.yonedaEquiv_symm_naturality_left,
      SSet.yonedaEquiv_symm_naturality_left]
    apply SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply]
    change X.map π.op b.simplex =
      (SSet.yonedaEquiv.symm x.simplex).app _ t.simplex
    change X.map s.toNπ.op s.toN.simplex = s.simplex
    exact SSet.S.map_toNπ_op_apply s
  change (SSet.sd.map (SSet.yonedaEquiv.symm b.simplex)).app _
      ((SSet.stdSimplex.sdIso.inv.app ⦋b.dim⦌).app _
        ((SimplexCategory.sd.map π).app _ Ft)) = _
  calc
    _ = (SSet.sd.map (SSet.yonedaEquiv.symm b.simplex)).app _
          ((SSet.sd.map (SSet.stdSimplex.map π)).app _ v) := by
      have hnat := SSet.stdSimplex.sdIso.inv.naturality π
      exact congrArg
        (fun f => (SSet.sd.map (SSet.yonedaEquiv.symm b.simplex)).app _
          (f.app _ Ft)) hnat
    _ = (SSet.sd.map (SSet.stdSimplex.map π ≫
          SSet.yonedaEquiv.symm b.simplex)).app _ v := by
      change ((SSet.sd.map (SSet.stdSimplex.map π) ≫
        SSet.sd.map (SSet.yonedaEquiv.symm b.simplex)).app _) v = _
      rw [← SSet.sd.map_comp]
    _ = (SSet.sd.map (SSet.stdSimplex.map μ ≫
          SSet.yonedaEquiv.symm x.simplex)).app _ v := by rw [hchar]
    _ = (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _
          ((SSet.sd.map (SSet.stdSimplex.map μ)).app _ v) := by
      change _ = ((SSet.sd.map (SSet.stdSimplex.map μ) ≫
        SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _) v
      rw [← SSet.sd.map_comp]
    _ = (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _
          ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _
            ((SimplexCategory.sd.map μ).app _ Ft)) := by
      have hnat := SSet.stdSimplex.sdIso.inv.naturality μ
      exact congrArg
        (fun f => (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _
          (f.app _ Ft)) hnat.symm
    _ = _ := by rw [hflag]

set_option maxHeartbeats 2000000 in
-- The quotient-invariance proof combines two Eilenberg--Zilber uniqueness
-- arguments and needs more than Lean's default elaboration budget.
private theorem sdNormalizeRepresentative_map {X : SSet.{u}}
    {m n : SimplexCategory} (f : m ⟶ n) (y : X.obj (op n))
    {d : ℕ} (F : (SimplexCategory.sd.{u}.obj m) _⦋d⦌) :
    sdNormalizeRepresentative (SSet.S.mk (X.map f.op y)) F =
      sdNormalizeRepresentative (SSet.S.mk y)
        ((SimplexCategory.sd.map f).app _ F) := by
  let xs : X.S := SSet.S.mk (X.map f.op y)
  let ys : X.S := SSet.S.mk y
  let F' := (SimplexCategory.sd.map f).app (op ⦋d⦌) F
  let c := sdFlagCarrierChain m F
  let c' := sdFlagCarrierChain n F'
  have hc' : c' =
      (SSet.nondegenerateNerve.map (SSet.stdSimplex.map f)).app _ c :=
    sdFlagCarrierChain_map f F
  let t := c.obj (Fin.last d)
  let rS : (Δ[n.len] : SSet.{u}).S :=
    SSet.S.mk ((SSet.stdSimplex.map f).app _ t.simplex)
  let t' := rS.toN
  let r : ⦋t.dim⦌ ⟶ ⦋t'.dim⦌ := rS.toNπ
  have ht' : c'.obj (Fin.last d) = t' := by
    rw [hc']
    rfl
  let L := anchoredLiftCarrierChain c
  let L' : (CategoryTheory.nerve
      (Δ[t'.dim] : SSet.{u}).N) _⦋d⦌ :=
    cast (congrArg (fun z : (Δ[n.len] : SSet.{u}).N =>
      (CategoryTheory.nerve
        (Δ[z.dim] : SSet.{u}).N) _⦋d⦌) ht')
      (anchoredLiftCarrierChain c')
  have hface : SSet.stdSimplex.map r ≫
        SSet.yonedaEquiv.symm t'.simplex =
      SSet.yonedaEquiv.symm t.simplex ≫
        SSet.stdSimplex.map f := by
    rw [SSet.yonedaEquiv_symm_naturality_left,
      SSet.yonedaEquiv_symm_comp]
    apply SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply]
    change (Δ[n.len] : SSet.{u}).map r.op t'.simplex =
      (SSet.stdSimplex.map f).app _ t.simplex
    change (Δ[n.len] : SSet.{u}).map rS.toNπ.op rS.toN.simplex =
      rS.simplex
    exact SSet.S.map_toNπ_op_apply rS
  have hL :
      (SSet.nondegenerateNerve.map (SSet.stdSimplex.map r)).app _ L = L' := by
    let χ := SSet.yonedaEquiv.symm t'.simplex
    let ψ := SSet.yonedaEquiv.symm t.simplex
    let _ : Mono χ := SSet.Nonsingular.mono'
      t'.simplex t'.nonDegenerate
    have hRight : (SSet.nondegenerateNerve.map χ).app _ L' = c' := by
      exact anchoredMap_liftCarrierChain_of_last_eq c' t' ht'
    apply anchoredNerve_map_injective_of_mono χ
    calc
      (SSet.nondegenerateNerve.map χ).app _
          ((SSet.nondegenerateNerve.map
            (SSet.stdSimplex.map r)).app _ L) =
          (SSet.nondegenerateNerve.map
            (SSet.stdSimplex.map r ≫ χ)).app _ L := by
        exact (congrArg
          (fun q => q.app (op ⦋d⦌) L)
          (SSet.nondegenerateNerve.map_comp
            (SSet.stdSimplex.map r) χ)).symm
      _ = (SSet.nondegenerateNerve.map
            (ψ ≫ SSet.stdSimplex.map f)).app _ L := by
        exact congrArg
          (fun q => (SSet.nondegenerateNerve.map q).app (op ⦋d⦌) L)
          (by simpa only [ψ] using hface)
      _ = (SSet.nondegenerateNerve.map
            (SSet.stdSimplex.map f)).app _
              ((SSet.nondegenerateNerve.map ψ).app _ L) := by
        exact congrArg
          (fun q => q.app (op ⦋d⦌) L)
          (SSet.nondegenerateNerve.map_comp ψ
            (SSet.stdSimplex.map f))
      _ = (SSet.nondegenerateNerve.map
            (SSet.stdSimplex.map f)).app _ c := by
        rw [anchoredMap_liftCarrierChain]
      _ = (SSet.nondegenerateNerve.map χ).app _ L' :=
        hc'.symm.trans hRight.symm
  let Ft := sdFlagOfCarrierChain ⦋t.dim⦌ L
  let Ft' := sdFlagOfCarrierChain ⦋t'.dim⦌ L'
  have hFt : (SimplexCategory.sd.map r).app _ Ft = Ft' := by
    rw [sdFlagOfCarrierChain_map]
    exact congrArg (sdFlagOfCarrierChain ⦋t'.dim⦌) hL
  let s : X.S := SSet.S.mk
    ((SSet.yonedaEquiv.symm (X.map f.op y)).app _ t.simplex)
  let s' : X.S := SSet.S.mk
    ((SSet.yonedaEquiv.symm y).app _ t'.simplex)
  have hs : X.map r.op s'.simplex = s.simplex := by
    change X.map r.op
        ((SSet.yonedaEquiv.symm y).app _ t'.simplex) =
      (SSet.yonedaEquiv.symm (X.map f.op y)).app _ t.simplex
    rw [← NatTrans.naturality_apply]
    have h := congrArg
      (fun g => g.app (op ⦋t.dim⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋t.dim⦌)))
      (Category.assoc (SSet.stdSimplex.map r)
        (SSet.yonedaEquiv.symm t'.simplex)
        (SSet.yonedaEquiv.symm y))
    rw [hface] at h
    simp only [NatTrans.comp_app_apply] at h
    simp only [SSet.yonedaEquiv_symm_app] at h
    rw [stdSimplex_objEquiv_map_apply r
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋t.dim⦌))] at h
    simp only [Equiv.apply_symm_apply, Category.id_comp,
      CategoryTheory.op_id, Functor.map_id_apply] at h
    rw [stdSimplex_objEquiv_map_apply f t.simplex] at h
    simpa [SSet.stdSimplex.map_apply,
      ← Functor.map_comp_apply, ← op_comp] using h.symm
  have hsDef : normalizedTerminalSimplex xs F = s := by
    rfl
  have hsDef' : normalizedTerminalSimplex ys F' = s' := by
    unfold normalizedTerminalSimplex
    change SSet.S.mk
      ((SSet.yonedaEquiv.symm y).app _
        (c'.obj (Fin.last d)).simplex) = s'
    rw [ht']
  have hb : s.toN = s'.toN := by
    rw [SSet.S.toN_eq_iff, SSet.S.subcomplex_toN]
    exact (SSet.S.subcomplex_eq_of_epi s s' r hs).symm
  have hdim : s.toN.dim = s'.toN.dim :=
    congrArg (fun z : X.N => z.dim) hb
  have hObj : ⦋s.toN.dim⦌ = ⦋s'.toN.dim⦌ :=
    congrArg (fun n : ℕ => ⦋n⦌) hdim
  have hType : X _⦋s.toN.dim⦌ = X _⦋s'.toN.dim⦌ :=
    congrArg (fun n : ℕ => X _⦋n⦌) hdim
  have hsimplex : HEq s.toN.simplex s'.toN.simplex :=
    congr_arg_heq (fun z : X.N => z.simplex) hb
  have hcast : cast hType s.toN.simplex = s'.toN.simplex :=
    eq_of_heq ((cast_heq_iff_heq hType _ _).2 hsimplex)
  have htransport : X.map (CategoryTheory.eqToHom hObj.symm).op
      s.toN.simplex = s'.toN.simplex := by
    rw [map_eqToHom_dim_apply hdim]
    exact hcast
  have hcomp : X.map (r ≫ s'.toNπ).op s'.toN.simplex = s.simplex := by
    rw [op_comp, Functor.map_comp_apply,
      SSet.S.map_toNπ_op_apply, hs]
  have hcomp' : X.map
      ((r ≫ s'.toNπ) ≫ CategoryTheory.eqToHom hObj.symm).op
        s.toN.simplex = s.simplex := by
    rw [op_comp, Functor.map_comp_apply, htransport]
    exact hcomp
  have hπ : HEq s.toNπ (r ≫ s'.toNπ) := by
    apply (CategoryTheory.conj_eqToHom_iff_heq
      s.toNπ (r ≫ s'.toNπ) rfl hObj).mp
    simp only [CategoryTheory.eqToHom_refl, Category.id_comp]
    exact X.unique_nonDegenerate_map s.simplex s.toNπ
      ⟨s.toN.simplex, s.toN.nonDegenerate⟩
      (SSet.S.map_toNπ_op_apply s).symm
      ((r ≫ s'.toNπ) ≫ CategoryTheory.eqToHom hObj.symm)
      ⟨s.toN.simplex, s.toN.nonDegenerate⟩ hcomp'.symm
  apply SdAnchoredFlag.ext
  · change (normalizedTerminalSimplex xs F).toN =
      (normalizedTerminalSimplex ys F').toN
    rw [hsDef, hsDef']
    exact hb
  · unfold sdNormalizeRepresentative normalizedFlag
    have hFlag' : HEq
        (sdFlagOfCarrierChain ⦋(c'.obj (Fin.last d)).dim⦌
          (anchoredLiftCarrierChain c')) Ft' :=
      sdFlagLift_of_last_eq c' t' ht'
    have hfirst := sdMap_apply_heq s.toNπ (r ≫ s'.toNπ)
      Ft Ft rfl hdim hπ HEq.rfl
    have hcompFlag :
        (SimplexCategory.sd.map (r ≫ s'.toNπ)).app _ Ft =
          (SimplexCategory.sd.map s'.toNπ).app _ Ft' := by
      calc
        _ = (SimplexCategory.sd.map s'.toNπ).app _
              ((SimplexCategory.sd.map r).app _ Ft) := by
          exact congrArg (fun q => q.app (op ⦋d⦌) Ft)
            (SimplexCategory.sd.map_comp r s'.toNπ)
        _ = _ := congrArg
          (fun q => (SimplexCategory.sd.map s'.toNπ).app _ q) hFt
    have hmain := hfirst.trans (heq_of_eq hcompFlag)
    have hπLeft : HEq
        (normalizedTerminalSimplex xs F).toNπ s.toNπ :=
      congr_arg_heq (fun q : X.S => q.toNπ) hsDef
    have hπRight : HEq
        (normalizedTerminalSimplex ys F').toNπ s'.toNπ :=
      congr_arg_heq (fun q : X.S => q.toNπ) hsDef'
    have hleft := sdMap_apply_heq
      (normalizedTerminalSimplex xs F).toNπ s.toNπ
      (sdFlagOfCarrierChain ⦋(c.obj (Fin.last d)).dim⦌
        (anchoredLiftCarrierChain c)) Ft
      (congrArg SSet.S.dim hsDef)
      (congrArg (fun z : X.N => z.dim)
        (congrArg SSet.S.toN hsDef)) hπLeft HEq.rfl
    have hright := sdMap_apply_heq
      (normalizedTerminalSimplex ys F').toNπ s'.toNπ
      (sdFlagOfCarrierChain ⦋(c'.obj (Fin.last d)).dim⦌
        (anchoredLiftCarrierChain c')) Ft'
      (congrArg SSet.S.dim hsDef')
      (congrArg (fun z : X.N => z.dim)
        (congrArg SSet.S.toN hsDef')) hπRight hFlag'
    exact hleft.trans hmain |>.trans hright.symm

private noncomputable abbrev sdPresentationDiagram
    (X : SSet.{u}) (d : ℕ) :=
  ((CostructuredArrow.proj SSet.stdSimplex X ⋙
      SSet.stdSimplex) ⋙ SSet.sd ⋙
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋d⦌))

private noncomputable def normalizeSigma (X : SSet.{u}) (d : ℕ)
    (z : Σ j, (sdPresentationDiagram X d).obj j) :
    SdAnchoredFlag X d :=
  sdNormalizeRepresentative
    (SSet.S.mk (SSet.yonedaEquiv z.1.hom))
    ((SSet.stdSimplex.sdIso.hom.app z.1.left).app _ z.2)

private theorem normalizeSigma_rel (X : SSet.{u}) (d : ℕ)
    {z z' : Σ j, (sdPresentationDiagram X d).obj j}
    (h : (sdPresentationDiagram X d).ColimitTypeRel z z') :
    normalizeSigma X d z = normalizeSigma X d z' := by
  obtain ⟨j, w⟩ := z
  obtain ⟨j', w'⟩ := z'
  rcases h with ⟨f, hf⟩
  dsimp only at hf ⊢
  have hx : SSet.yonedaEquiv j.hom =
      X.map f.left.op (SSet.yonedaEquiv j'.hom) := by
    rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f]
  have hF : (SSet.stdSimplex.sdIso.hom.app j'.left).app _
      ((sdPresentationDiagram X d).map f w) =
    (SimplexCategory.sd.map f.left).app _
      ((SSet.stdSimplex.sdIso.hom.app j.left).app _ w) := by
    have hnat := SSet.stdSimplex.sdIso.hom.naturality f.left
    have happ := congrArg (fun g => g.app (op ⦋d⦌) w) hnat
    exact happ
  have hF' : (SSet.stdSimplex.sdIso.hom.app j'.left).app _ w' =
      (SimplexCategory.sd.map f.left).app _
        ((SSet.stdSimplex.sdIso.hom.app j.left).app _ w) := by
    rw [hf]
    exact hF
  unfold normalizeSigma
  rw [hx, hF']
  exact sdNormalizeRepresentative_map f.left
    (SSet.yonedaEquiv j'.hom)
      ((SSet.stdSimplex.sdIso.hom.app j.left).app _ w)

private theorem normalizeSigma_eq_of_eqvGen (X : SSet.{u}) (d : ℕ)
    {z z' : Σ j, (sdPresentationDiagram X d).obj j}
    (h : Relation.EqvGen (sdPresentationDiagram X d).ColimitTypeRel z z') :
    normalizeSigma X d z = normalizeSigma X d z' := by
  induction h with
  | rel _ _ h => exact normalizeSigma_rel X d h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem sdNormalizeRepresentative_anchored {X : SSet.{u}} {d : ℕ}
    (a : SdAnchoredFlag X d) :
    sdNormalizeRepresentative a.carrier.toS a.flag = a := by
  let c := sdFlagCarrierChain ⦋a.carrier.dim⦌ a.flag
  have hs : normalizedTerminalSimplex a.carrier.toS a.flag =
      a.carrier.toS := by
    unfold normalizedTerminalSimplex
    rw [a.terminal_full]
    change SSet.S.mk
      ((SSet.yonedaEquiv.symm a.carrier.simplex).app _
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋a.carrier.dim⦌))) =
      a.carrier.toS
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    simp
  have hb : normalizedCarrier a.carrier.toS a.flag = a.carrier := by
    change (normalizedTerminalSimplex a.carrier.toS a.flag).toN = _
    rw [hs, SSet.S.toN_eq_iff]
  have hπ : HEq
      (normalizedTerminalSimplex a.carrier.toS a.flag).toNπ
      (𝟙 ⦋a.carrier.dim⦌) := by
    rw [hs]
    exact nondegenerate_toNπ_heq_id a.carrier
  have hlast : c.obj (Fin.last d) = sdTopCarrier a.carrier :=
    a.terminal_full
  have hL : HEq (anchoredLiftCarrierChain c) c := by
    have htop :
        SSet.yonedaEquiv.symm (sdTopCarrier a.carrier).simplex =
          𝟙 (Δ[a.carrier.dim] : SSet.{u}) := by
      change SSet.yonedaEquiv.symm
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋a.carrier.dim⦌)) = _
      exact SSet.yonedaEquiv_symm_stdSimplex_id.{u}
        ⦋a.carrier.dim⦌
    have hType :
        (CategoryTheory.nerve
          (Δ[(c.obj (Fin.last d)).dim] : SSet.{u}).N) _⦋d⦌ =
        (CategoryTheory.nerve
          (Δ[a.carrier.dim] : SSet.{u}).N) _⦋d⦌ :=
      congrArg (fun z : (Δ[a.carrier.dim] : SSet.{u}).N =>
        (CategoryTheory.nerve
          (Δ[z.dim] : SSet.{u}).N) _⦋d⦌) hlast
    let Lc : (CategoryTheory.nerve
        (Δ[a.carrier.dim] : SSet.{u}).N) _⦋d⦌ :=
      cast hType (anchoredLiftCarrierChain c)
    have hLc : HEq (anchoredLiftCarrierChain c) Lc :=
      (cast_heq hType (anchoredLiftCarrierChain c)).symm
    have hmap := anchoredMap_liftCarrierChain_of_last_eq c
      (sdTopCarrier a.carrier) hlast
    rw [htop] at hmap
    change (SSet.nondegenerateNerve.map
      (𝟙 (Δ[a.carrier.dim] : SSet.{u}))).app _ Lc = c at hmap
    have hid : (SSet.nondegenerateNerve.map
        (𝟙 (Δ[a.carrier.dim] : SSet.{u}))).app _ Lc = Lc := by
      have h := congrArg (fun q => q.app (op ⦋d⦌) Lc)
        (SSet.nondegenerateNerve.map_id
          (Δ[a.carrier.dim] : SSet.{u}))
      exact h.trans (CategoryTheory.id_apply
        (C := Type u)
        (X := (SSet.nondegenerateNerve.obj
          (Δ[a.carrier.dim] : SSet.{u})) _⦋d⦌) Lc)
    exact hLc.trans (heq_of_eq (hid.symm.trans hmap))
  apply SdAnchoredFlag.ext
  · exact hb
  · change HEq
      ((SimplexCategory.sd.map
        (normalizedTerminalSimplex a.carrier.toS a.flag).toNπ).app _
          (sdFlagOfCarrierChain
            ⦋((sdFlagCarrierChain ⦋a.carrier.dim⦌ a.flag).obj
              (Fin.last d)).dim⦌
            (anchoredLiftCarrierChain c))) a.flag
    have hsDim : (normalizedTerminalSimplex
        a.carrier.toS a.flag).dim = a.carrier.dim :=
      congrArg SSet.S.dim hs
    have hbDim : (normalizedTerminalSimplex
        a.carrier.toS a.flag).toN.dim = a.carrier.dim :=
      congrArg (fun z : X.N => z.dim) hb
    have hlDim : (c.obj (Fin.last d)).dim = a.carrier.dim :=
      congrArg (fun z : (Δ[a.carrier.dim] : SSet.{u}).N => z.dim) hlast
    have hFlag := sdFlagOfCarrierChain_heq
      (anchoredLiftCarrierChain c) c hlDim hL
    have hNorm := sdMap_apply_heq
      (normalizedTerminalSimplex a.carrier.toS a.flag).toNπ
      (𝟙 ⦋a.carrier.dim⦌)
      (sdFlagOfCarrierChain ⦋(c.obj (Fin.last d)).dim⦌
        (anchoredLiftCarrierChain c))
      (sdFlagOfCarrierChain ⦋a.carrier.dim⦌ c)
      hsDim hbDim hπ hFlag
    refine hNorm.trans (heq_of_eq ?_)
    calc
      _ = sdFlagOfCarrierChain ⦋a.carrier.dim⦌ c := by
        have hid := congrArg
          (fun q => q.app (op ⦋d⦌)
            (sdFlagOfCarrierChain ⦋a.carrier.dim⦌ c))
          (SimplexCategory.sd.map_id ⦋a.carrier.dim⦌)
        simpa only [NatTrans.id_app, CategoryTheory.id_apply] using hid
      _ = a.flag := sdFlagOfCarrierChain_flagCarrierChain
        ⦋a.carrier.dim⦌ a.flag

private noncomputable abbrev anchoredPresentObj {X : SSet.{u}} {d : ℕ}
    (a : SdAnchoredFlag X d) :
    CostructuredArrow SSet.stdSimplex X :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm a.carrier.simplex)

private noncomputable abbrev anchoredPresentPoint {X : SSet.{u}} {d : ℕ}
    (a : SdAnchoredFlag X d) :
    (sdPresentationDiagram X d).obj (anchoredPresentObj a) :=
  (SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag

private theorem normalizeSigma_anchored {X : SSet.{u}} {d : ℕ}
    (a : SdAnchoredFlag X d) :
    normalizeSigma X d ⟨anchoredPresentObj a, anchoredPresentPoint a⟩ = a := by
  unfold normalizeSigma anchoredPresentPoint anchoredPresentObj
  change sdNormalizeRepresentative
      (SSet.S.mk (SSet.yonedaEquiv
        (CostructuredArrow.mk
          (SSet.yonedaEquiv.symm a.carrier.simplex)).hom))
      ((SSet.stdSimplex.sdIso.hom.app ⦋a.carrier.dim⦌).app _
        ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag)) = a
  have hhom :
      (CostructuredArrow.mk
        (SSet.yonedaEquiv.symm a.carrier.simplex)).hom =
      SSet.yonedaEquiv.symm a.carrier.simplex :=
    CostructuredArrow.mk_hom_eq_self _
  rw [hhom, Equiv.apply_symm_apply]
  have hsd : (SSet.stdSimplex.sdIso.hom.app ⦋a.carrier.dim⦌).app _
      ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag) =
    a.flag := by
    change ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌ ≫
      SSet.stdSimplex.sdIso.hom.app ⦋a.carrier.dim⦌).app _) a.flag = _
    rw [Iso.inv_hom_id_app]
    rfl
  rw [hsd]
  exact sdNormalizeRepresentative_anchored a

private theorem anchoredPresentPoint_maps_toSimplex {X : SSet.{u}} {d : ℕ}
    (a : SdAnchoredFlag X d) :
    (((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋d⦌)).mapCocone
      (SSet.sd.mapCocone
        ({ pt := X, ι := { app j := j.hom } } :
          Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙ uliftYoneda.{u})))).ι.app
        (anchoredPresentObj a) (anchoredPresentPoint a) = a.toSimplex := by
  rfl

/-- Anchored representatives are unique in every subdivision degree.  The
proof uses the generated coend relation, not a chosen quotient section. -/
theorem SdAnchoredFlag.toSimplex_injective (X : SSet.{u}) (d : ℕ) :
    Function.Injective
      (SdAnchoredFlag.toSimplex : SdAnchoredFlag X d →
        (SSet.sd.obj X) _⦋d⦌) := by
  intro a b hab
  let c : Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙ uliftYoneda.{u}) :=
    { pt := X, ι := { app j := j.hom } }
  have hc : IsColimit c := denseAtUliftYoneda.{u} X
  have hsd : IsColimit (SSet.sd.mapCocone c) :=
    isColimitOfPreserves SSet.sd hc
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋d⦌)
  have hev : IsColimit (ev.mapCocone (SSet.sd.mapCocone c)) :=
    isColimitOfPreserves ev hsd
  let ct := (sdPresentationDiagram X d).coconeTypesEquiv.symm
    (ev.mapCocone (SSet.sd.mapCocone c))
  have hct : ct.IsColimit :=
    (Types.isColimit_iff_coconeTypesIsColimit _).1 ⟨hev⟩
  have hcol : (sdPresentationDiagram X d).ιColimitType
        (anchoredPresentObj a) (anchoredPresentPoint a) =
      (sdPresentationDiagram X d).ιColimitType
        (anchoredPresentObj b) (anchoredPresentPoint b) := by
    rw [← hct.equiv_symm_ι_apply, ← hct.equiv_symm_ι_apply]
    apply congrArg hct.equiv.symm
    change a.toSimplex = b.toSimplex
    exact hab
  have heqv := ((sdPresentationDiagram X d).ιColimitType_eq_iff
    (anchoredPresentPoint a) (anchoredPresentPoint b)).mp hcol
  have hnorm := normalizeSigma_eq_of_eqvGen X d heqv
  rw [normalizeSigma_anchored, normalizeSigma_anchored] at hnorm
  exact hnorm

/-- Every subdivision simplex has an anchored representative. -/
theorem SdAnchoredFlag.toSimplex_surjective (X : SSet.{u}) (d : ℕ) :
    Function.Surjective
      (SdAnchoredFlag.toSimplex : SdAnchoredFlag X d →
        (SSet.sd.obj X) _⦋d⦌) := by
  let c : Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙ uliftYoneda.{u}) :=
    { pt := X, ι := { app j := j.hom } }
  have hc : IsColimit c := denseAtUliftYoneda.{u} X
  have hsd : IsColimit (SSet.sd.mapCocone c) :=
    isColimitOfPreserves SSet.sd hc
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋d⦌)
  have hev : IsColimit (ev.mapCocone (SSet.sd.mapCocone c)) :=
    isColimitOfPreserves ev hsd
  intro z
  obtain ⟨j, w, hw⟩ := Types.jointly_surjective_of_isColimit hev z
  let x : X.S := SSet.S.mk (CategoryTheory.uliftYonedaEquiv j.hom)
  let F : (SimplexCategory.sd.{u}.obj j.left) _⦋d⦌ :=
    (SSet.stdSimplex.sdIso.hom.app j.left).app _ w
  refine ⟨sdNormalizeRepresentative x F, ?_⟩
  rw [sdNormalizeRepresentative_toSimplex]
  have hsdIso : (SSet.stdSimplex.sdIso.inv.app j.left).app _ F = w := by
    change (SSet.stdSimplex.sdIso.inv.app j.left).app _
      ((SSet.stdSimplex.sdIso.hom.app j.left).app _ w) = w
    change ((SSet.stdSimplex.sdIso.hom.app j.left ≫
      SSet.stdSimplex.sdIso.inv.app j.left).app (op ⦋d⦌)) w = w
    rw [Iso.hom_inv_id_app]
    rfl
  rw [hsdIso]
  have hx : SSet.yonedaEquiv.symm x.simplex = j.hom := by
    change CategoryTheory.uliftYonedaEquiv.symm x.simplex = j.hom
    dsimp [x]
    exact Equiv.symm_apply_apply CategoryTheory.uliftYonedaEquiv j.hom
  rw [hx]
  exact hw

/-- Degreewise anchored normal form for subdivision of an arbitrary
simplicial set. -/
noncomputable def sdAnchoredEquiv (X : SSet.{u}) (d : ℕ) :
    (SSet.sd.obj X) _⦋d⦌ ≃ SdAnchoredFlag X d :=
  (Equiv.ofBijective SdAnchoredFlag.toSimplex
    ⟨SdAnchoredFlag.toSimplex_injective X d,
      SdAnchoredFlag.toSimplex_surjective X d⟩).symm

@[simp]
theorem sdAnchoredEquiv_symm_apply (X : SSet.{u}) (d : ℕ)
    (a : SdAnchoredFlag X d) :
    (sdAnchoredEquiv X d).symm a = a.toSimplex :=
  rfl

@[simp]
theorem SdAnchoredFlag.equiv_toSimplex {X : SSet.{u}} {d : ℕ}
    (a : SdAnchoredFlag X d) :
    sdAnchoredEquiv X d a.toSimplex = a :=
  (sdAnchoredEquiv X d).apply_symm_apply a

/-- Explicit normalization formula on every standard-simplex representative.
This is the quotient-invariant inverse, not a chosen presentation. -/
theorem sdAnchoredEquiv_map_standard {X : SSet.{u}} {d : ℕ}
    (x : X.S) (F : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌) :
    sdAnchoredEquiv X d
      ((SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _
        ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ F)) =
      sdNormalizeRepresentative x F := by
  apply SdAnchoredFlag.toSimplex_injective X d
  exact ((sdAnchoredEquiv X d).symm_apply_apply _).trans
    (sdNormalizeRepresentative_toSimplex x F).symm

namespace SdAnchoredFlag

variable {X : SSet.{u}} {d e : ℕ}

/-- The branch in which an operator hits the last flag position. -/
noncomputable def mapHitLast (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌)
    (h : f.toOrderHom (Fin.last e) = Fin.last d) :
    SdAnchoredFlag X e where
  carrier := a.carrier
  flag := (SimplexCategory.sd.obj ⦋a.carrier.dim⦌).map f.op a.flag
  terminal_full := by
    rw [sdFlagCarrierChain_obj_map]
    change (sdFlagCarrierChain ⦋a.carrier.dim⦌ a.flag).obj
      (f.toOrderHom (Fin.last e)) = sdTopCarrier a.carrier
    rw [h]
    exact a.terminal_full

/-- The non-last-hitting branch reruns terminal-face normalization. -/
noncomputable def mapMissLast (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌) : SdAnchoredFlag X e :=
  sdNormalizeRepresentative a.carrier.toS
    ((SimplexCategory.sd.obj ⦋a.carrier.dim⦌).map f.op a.flag)

/-- Simplicial operator on anchored normal forms, with the last-hitting and
renormalizing branches exposed. -/
noncomputable def map (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌) : SdAnchoredFlag X e :=
  if h : f.toOrderHom (Fin.last e) = Fin.last d then
    a.mapHitLast f h
  else
    a.mapMissLast f

@[simp]
theorem map_of_hitsLast (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌)
    (h : f.toOrderHom (Fin.last e) = Fin.last d) :
    a.map f = a.mapHitLast f h := by
  simp [map, h]

@[simp]
theorem map_of_not_hitsLast (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌)
    (h : f.toOrderHom (Fin.last e) ≠ Fin.last d) :
    a.map f = a.mapMissLast f := by
  simp [map, h]

private theorem toSimplex_flag_map (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌) :
    (SSet.sd.map (SSet.yonedaEquiv.symm a.carrier.simplex)).app _
        ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _
          ((SimplexCategory.sd.obj ⦋a.carrier.dim⦌).map f.op a.flag)) =
      (SSet.sd.obj X).map f.op a.toSimplex := by
  unfold toSimplex
  calc
    _ = (SSet.sd.map (SSet.yonedaEquiv.symm a.carrier.simplex)).app _
          ((SSet.sd.obj (Δ[a.carrier.dim] : SSet.{u})).map f.op
            ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _
              a.flag)) := by
        congr 1
        exact ConcreteCategory.congr_hom
          ((SSet.stdSimplex.sdIso.inv.app
            ⦋a.carrier.dim⦌).naturality f.op) a.flag
    _ = _ := ConcreteCategory.congr_hom
      ((SSet.sd.map
        (SSet.yonedaEquiv.symm a.carrier.simplex)).naturality f.op) _

/-- Operator formula on encoded anchored representatives. -/
theorem toSimplex_map (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌) :
    (a.map f).toSimplex = (SSet.sd.obj X).map f.op a.toSimplex := by
  by_cases h : f.toOrderHom (Fin.last e) = Fin.last d
  · rw [a.map_of_hitsLast f h]
    exact a.toSimplex_flag_map f
  · rw [a.map_of_not_hitsLast f h, mapMissLast,
      sdNormalizeRepresentative_toSimplex]
    exact a.toSimplex_flag_map f

/-- The degreewise equivalence intertwines every simplex operator with the
explicit anchored operator. -/
theorem equiv_obj_map (a : SdAnchoredFlag X d)
    (f : ⦋e⦌ ⟶ ⦋d⦌) :
    sdAnchoredEquiv X e ((SSet.sd.obj X).map f.op a.toSimplex) = a.map f := by
  apply SdAnchoredFlag.toSimplex_injective X e
  rw [a.toSimplex_map]
  exact (sdAnchoredEquiv X e).symm_apply_apply _

private theorem epi_map_last {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] :
    f.toOrderHom (Fin.last m) = Fin.last n := by
  apply le_antisymm (Fin.le_last _)
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp
    (inferInstance : Epi f)) (Fin.last n)
  rw [← hi]
  exact f.toOrderHom.monotone (Fin.le_last i)

/-- An anchored subdivision simplex is nondegenerate exactly when its weak
face flag is strict. -/
theorem toSimplex_mem_nonDegenerate_iff (a : SdAnchoredFlag X d) :
    a.toSimplex ∈ (SSet.sd.obj X).nonDegenerate d ↔ StrictMono a.flag.obj := by
  constructor
  · intro ha
    by_contra hflag
    have hnotmem : a.flag ∉
        (SimplexCategory.sd.obj ⦋a.carrier.dim⦌).nonDegenerate d := by
      intro hmem
      exact hflag
        ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono a.flag).mp hmem)
    have hdeg : a.flag ∈
        (SimplexCategory.sd.obj ⦋a.carrier.dim⦌).degenerate d :=
      (SSet.mem_degenerate_iff_notMem_nonDegenerate _ a.flag).2 hnotmem
    obtain ⟨m, hm, f, hf, ⟨G, hG⟩⟩ :=
      (SSet.mem_degenerate_iff _ a.flag).1 hdeg
    let _ : Epi f := hf
    have hlast := epi_map_last f
    let b : SdAnchoredFlag X m :=
      { carrier := a.carrier
        flag := G
        terminal_full := by
          have hchain := sdFlagCarrierChain_obj_map
            ⦋a.carrier.dim⦌ f G
          have hterminal := a.terminal_full
          rw [← hG, hchain] at hterminal
          change (sdFlagCarrierChain ⦋a.carrier.dim⦌ G).obj
            (f.toOrderHom (Fin.last d)) = sdTopCarrier a.carrier at hterminal
          rwa [hlast] at hterminal }
    have hmap : (SSet.sd.obj X).map f.op b.toSimplex = a.toSimplex := by
      rw [← b.toSimplex_flag_map f, hG]
      rfl
    exact (SSet.mem_nonDegenerate_iff_notMem_degenerate _ a.toSimplex).1 ha
      ((SSet.mem_degenerate_iff _ a.toSimplex).2
        ⟨m, hm, f, hf, ⟨b.toSimplex, hmap⟩⟩)
  · intro hstrict
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
    intro hdeg
    obtain ⟨m, hm, f, hf, ⟨y, hy⟩⟩ :=
      (SSet.mem_degenerate_iff _ a.toSimplex).1 hdeg
    let _ : Epi f := hf
    let b := sdAnchoredEquiv X m y
    have hyb : b.toSimplex = y := by
      exact (sdAnchoredEquiv X m).symm_apply_apply y
    have hab : a = b.map f := by
      apply SdAnchoredFlag.toSimplex_injective X d
      rw [b.toSimplex_map, hyb]
      exact hy.symm
    have hlast := epi_map_last f
    rw [b.map_of_hitsLast f hlast] at hab
    have hmapStrict : StrictMono
        ((SimplexCategory.sd.obj ⦋b.carrier.dim⦌).map f.op b.flag).obj := by
      change StrictMono (b.mapHitLast f hlast).flag.obj
      exact Eq.mp
        (congrArg (fun z : SdAnchoredFlag X d => StrictMono z.flag.obj) hab)
        hstrict
    have hfinj : Function.Injective f.toOrderHom := by
      intro i j hij
      apply hmapStrict.injective
      change b.flag.obj (f.toOrderHom i) = b.flag.obj (f.toOrderHom j)
      rw [hij]
    let _ : Mono f := SimplexCategory.mono_iff_injective.mpr hfinj
    let _ : IsIso f := isIso_of_mono_of_epi f
    exact (Nat.ne_of_lt hm) (SimplexCategory.eq_of_isIso f).symm

/-- Degeneracy is exactly repetition of an adjacent face in the weak flag. -/
theorem toSimplex_mem_degenerate_iff (a : SdAnchoredFlag X d) :
    a.toSimplex ∈ (SSet.sd.obj X).degenerate d ↔
      ∃ i : Fin d, a.flag.obj i.castSucc = a.flag.obj i.succ := by
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate,
    a.toSimplex_mem_nonDegenerate_iff, Fin.strictMono_iff_lt_succ]
  push Not
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, eq_of_le_of_not_lt
      (a.flag.monotone i.castSucc_le_succ) hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi]; exact lt_irrefl _⟩

end SdAnchoredFlag

namespace SdAnchoredFlag

variable {X : SSet.{u}} {d : ℕ}

/-- Last vertex on an anchored representative is obtained by applying the
carrier characteristic map to the representable last-vertex simplex.  The
coordinate maxima are given by `SSet.lastVertex_stdSimplex_apply`. -/
theorem lastVertex_toSimplex (a : SdAnchoredFlag X d) :
    (SSet.lastVertex.app X).app _ a.toSimplex =
      (SSet.yonedaEquiv.symm a.carrier.simplex).app _
        ((SSet.lastVertex.app (Δ[a.carrier.dim] : SSet.{u})).app _
          ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag)) := by
  have hnat := SSet.lastVertex.naturality
    (SSet.yonedaEquiv.symm a.carrier.simplex)
  have happ := congrArg
    (fun f => f.app (op ⦋d⦌)
      ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag)) hnat
  change (SSet.lastVertex.app X).app _ a.toSimplex = _
  exact happ

/-- Coordinate form of the last-vertex characteristic law. -/
theorem lastVertex_toSimplex_vertex (a : SdAnchoredFlag X d)
    (i : Fin (d + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋d⦌ i).op
        ((SSet.lastVertex.app X).app _ a.toSimplex) =
      (SSet.yonedaEquiv.symm a.carrier.simplex).app _
        (SSet.stdSimplex.obj₀Equiv.symm
          (SimplexCategory.sdChainLast ⦋a.carrier.dim⦌
            (a.flag.obj i)).down) := by
  rw [a.lastVertex_toSimplex, ← NatTrans.naturality_apply]
  congr 1
  apply SSet.stdSimplex.obj₀Equiv.injective
  exact SSet.lastVertex_stdSimplex_apply ⦋a.carrier.dim⦌ a.flag i

/-- Barratt comparison on an anchored representative is the mapped chain of
its actual standard-simplex face carriers. Repeated values are retained. -/
theorem sdToNondegenerateNerve_toSimplex (a : SdAnchoredFlag X d) :
    (SSet.sdToNondegenerateNerve.app X).app _ a.toSimplex =
      (SSet.nondegenerateNerve.map
        (SSet.yonedaEquiv.symm a.carrier.simplex)).app _
          (sdFlagCarrierChain ⦋a.carrier.dim⦌ a.flag) := by
  have hnat := SSet.sdToNondegenerateNerve.naturality
    (SSet.yonedaEquiv.symm a.carrier.simplex)
  have happ := congrArg
    (fun f => f.app (op ⦋d⦌)
      ((SSet.stdSimplex.sdIso.inv.app ⦋a.carrier.dim⦌).app _ a.flag)) hnat
  exact happ

end SdAnchoredFlag

end SSet

end
