/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing morphisms of module sheaves over open covers

Let `S : Type u` be a topological space, `R` a sheaf of rings with carrier universe `v`, and
`M,N` module sheaves with carrier universe `w`. Morphisms `M.over U_i → N.over U_i` on an open
cover glue to a global module-sheaf morphism when their restrictions agree on every pairwise
intersection `U_i ∩ U_j`.

A cover also detects equality of global morphisms. The restriction maps use the canonical
comparisons between an over-site restriction and the corresponding slice morphism. The space,
ring, module, and cover-index universes are independent.
-/

/-
The open-cover proof is extracted from
`MathlibExt.AlgebraicGeometry.Modules.InvertibleTensorPullback` at the
qualified source revision `d72659cad892b9a78aa0edcf0dddc1aeafc9a4a4`.
The original generic API was in `AlgebraicGeometry.Modules.HomGluing` at
revision `5bb6805e49f68816583d28eaee16b423375a788e`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u v w z
namespace SheafOfModules

theorem exists_gluedAbHom {S : Type u} [TopologicalSpace S]
    (F G : (_root_.TopologicalSpace.Opens S)ᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : CategoryTheory.Presheaf.IsSheaf (_root_.Opens.grothendieckTopology S) G)
    {I : Type z} (U : I → _root_.TopologicalSpace.Opens S)
    (hU : (_root_.Opens.grothendieckTopology S).CoversTop U)
    (a : ∀ i, (presheafHom F G).obj (op (U i)))
    (ha : TopCat.Presheaf.IsCompatible (X := TopCat.of S) (presheafHom F G) U a) :
    ∃ h : F ⟶ G, ∀ i, Functor.whiskerLeft (Over.forget (U i)).op h = a i := by
  let H : (_root_.TopologicalSpace.Opens S)ᵒᵖ ⥤ Type (max u v) := presheafHom F G
  have hH : (show TopCat.Presheaf (Type (max u v)) (TopCat.of S) from H).IsSheaf :=
    CategoryTheory.Presheaf.IsSheaf.hom F G hG
  obtain ⟨s, hs, _⟩ := hH.isSheafUniqueGluing U a ha
  have htop : iSup U = ⊤ := (_root_.Opens.coversTop_iff S U).mp hU
  let g (V : _root_.TopologicalSpace.Opens S) : V ⟶ iSup U := homOfLE (htop.symm ▸ le_top)
  let t : H.sections :=
    { val := fun V => H.map (g V.unop).op s
      property := fun f => by
        dsimp
        rw [← Functor.map_comp_apply]
        congr 1 }
  let h : F ⟶ G := presheafHomSectionsEquiv F G t
  refine ⟨h, fun i => ?_⟩
  have he : Functor.whiskerLeft (Over.forget (U i)).op h = t.val (op (U i)) := by
    exact congrArg (fun q : H.sections => q.val (op (U i)))
      ((presheafHomSectionsEquiv F G).left_inv t)
  apply he.trans
  change H.map (g (U i)).op s = a i
  exact (congrArg (fun k : U i ⟶ iSup U => H.map k.op s)
      (Subsingleton.elim (g (U i)) (homOfLE (le_iSup U i)))).trans (hs i)


/-- Let `S : Type u` be a topological space, `R` a ring sheaf of carrier universe `v`, and `M,N`
module sheaves with a common carrier universe `w`. For an inclusion `i : U → V` and `h :
M.over V → N.over V`, `overHomRestrict i h : M.over U → N.over U` is `((overFunctorMap R
i).app M).inv ≫ (overMap R i).map h ≫ ((overFunctorMap R i).app N).hom`, using the canonical
over-site comparisons. The universes `u,v,w` are independent. -/
def overHomRestrict {S : Type u} [TopologicalSpace S]
    {R : Sheaf (_root_.Opens.grothendieckTopology S) RingCat.{v}}
    {M N : SheafOfModules.{w} R} {U V : _root_.TopologicalSpace.Opens S} (i : U ⟶ V)
    (h : M.over V ⟶ N.over V) : M.over U ⟶ N.over U :=
  ((SheafOfModules.overFunctorMap R i).app M).inv ≫
    (SheafOfModules.overMap R i).map h ≫
    ((SheafOfModules.overFunctorMap R i).app N).hom

/-- Let `S : Type u` be a topological space, `R` a ring sheaf of carrier universe `v`, and `M,N`
module sheaves of common carrier universe `w`. For an open set `U` and `h : M.over U → N.over
U`, `overAbHom U h` is the section over `U` of `presheafHom M.val.presheaf N.val.presheaf`
obtained by forgetting the module action in `h`. It is a natural transformation of underlying
additive presheaves on the over-site; `u,v,w` are independent. -/
def overAbHom {S : Type u} [TopologicalSpace S]
    {R : Sheaf (_root_.Opens.grothendieckTopology S) RingCat.{v}}
    {M N : SheafOfModules.{w} R} (U : _root_.TopologicalSpace.Opens S) (h : M.over U ⟶ N.over U) :
    (presheafHom M.val.presheaf N.val.presheaf).obj (op U) :=
  (PresheafOfModules.toPresheaf (R.over U).obj).map h.val

theorem overAbHom_restrict {S : Type u} [TopologicalSpace S]
    {R : Sheaf (_root_.Opens.grothendieckTopology S) RingCat.{v}}
    {M N : SheafOfModules.{w} R} {U V : _root_.TopologicalSpace.Opens S} (i : U ⟶ V)
    (h : M.over V ⟶ N.over V) :
    (presheafHom M.val.presheaf N.val.presheaf).map i.op
        (overAbHom (R := R) (M := M) (N := N) V h) =
      overAbHom (R := R) (M := M) (N := N) U
        (overHomRestrict (R := R) (M := M) (N := N) i h) := by
  apply NatTrans.ext
  funext W
  ext m
  rfl

theorem exists_gluedModuleHom {S : Type u} [TopologicalSpace S]
    {R : Sheaf (_root_.Opens.grothendieckTopology S) RingCat.{v}}
    (M N : SheafOfModules.{w} R) {I : Type z} (U : I → _root_.TopologicalSpace.Opens S)
    (hU : (_root_.Opens.grothendieckTopology S).CoversTop U)
    (hi : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hc : ∀ i j, overHomRestrict (R := R) (M := M) (N := N)
        (TopologicalSpace.Opens.infLELeft (X := TopCat.of S) (U i) (U j)) (hi i) =
      overHomRestrict (R := R) (M := M) (N := N)
        (TopologicalSpace.Opens.infLERight (X := TopCat.of S) (U i) (U j)) (hi j)) :
    ∃ h : M ⟶ N, ∀ i, h.over (U i) = hi i := by
  let H : (_root_.TopologicalSpace.Opens S)ᵒᵖ ⥤ Type (max u w) := presheafHom M.val.presheaf N.val.presheaf
  let a (i : I) : H.obj (op (U i)) := overAbHom (R := R) (M := M) (N := N) (U i) (hi i)
  have ha : TopCat.Presheaf.IsCompatible (X := TopCat.of S) H U a := by
    intro i j
    dsimp only [a]
    rw [overAbHom_restrict (R := R) (M := M) (N := N),
      overAbHom_restrict (R := R) (M := M) (N := N)]
    exact congrArg (overAbHom (R := R) (M := M) (N := N) (U i ⊓ U j)) (hc i j)
  obtain ⟨α, hα⟩ := exists_gluedAbHom M.val.presheaf N.val.presheaf N.isSheaf U hU a ha
  have hlin : ∀ V : (_root_.TopologicalSpace.Opens S)ᵒᵖ, ∀ (r : R.obj.obj V) (m : M.val.obj V),
      α.app V (r • m) = r • α.app V m := by
    rintro ⟨V⟩ r m
    apply N.isSheaf.isSeparated _ _ (hU V)
    intro W v hv
    obtain ⟨i, ⟨w⟩⟩ := (Sieve.mem_ofObjects_iff U v).mp hv
    let aV : M.val.obj (op V) → N.val.obj (op V) := fun x => α.app (op V) x
    let aW : M.val.obj (op W) → N.val.obj (op W) := fun x => α.app (op W) x
    let mres : M.val.obj (op V) → M.val.obj (op W) := fun x => M.val.presheaf.map v.op x
    let nres : N.val.obj (op V) → N.val.obj (op W) := fun x => N.val.presheaf.map v.op x
    let fi : M.val.obj (op W) → N.val.obj (op W) :=
      fun x => (hi i).val.app (op (Over.mk w)) x
    have hn (x : M.val.obj (op V)) :
        nres (aV x) = aW (mres x) :=
      (CategoryTheory.congr_fun (α.naturality v.op) x).symm
    have hnsmul (s : R.obj.obj (op V)) (x : N.val.obj (op V)) :
        nres (s • x) = R.obj.map v.op s • nres x := N.val.map_smul v.op s x
    have hp (x : M.val.obj (op W)) :
        aW x = fi x :=
      CategoryTheory.congr_fun (NatTrans.congr_app (hα i) (op (Over.mk w))) x
    have hW (s : R.obj.obj (op W)) (x : M.val.obj (op W)) :
        aW (s • x) = s • aW x := by
      let s' : (R.over (U i)).obj.obj (op (Over.mk w)) := s
      have hfi : fi (s • x) = s • fi x :=
        ((hi i).val.app (op (Over.mk w))).hom.map_smul s' _
      calc
        _ = fi (s • x) := hp _
        _ = s • fi x := hfi
        _ = _ := congrArg (fun q : N.val.obj (op W) => s • q) (hp x).symm
    change nres (aV (r • m)) = nres (r • aV m)
    calc
      _ = aW (mres (r • m)) := hn _
      _ = aW (R.obj.map v.op r • mres m) :=
        congrArg aW (M.val.map_smul v.op r m)
      _ = R.obj.map v.op r • aW (mres m) := hW _ _
      _ = R.obj.map v.op r • nres (aV m) :=
        congrArg (fun q : N.val.obj (op W) => R.obj.map v.op r • q) (hn m).symm
      _ = _ := (hnsmul r (aV m)).symm
  let h : M ⟶ N := ⟨PresheafOfModules.homMk α hlin⟩
  refine ⟨h, fun i => ?_⟩
  ext V m
  exact CategoryTheory.congr_fun (NatTrans.congr_app (hα i) V) m

/-- Let `S : Type u` be a topological space, `R` a ring sheaf of carrier universe `v`, `M,N`
module sheaves of carrier universe `w`, and `a,b : M → N`. For `I : Type z` and `U : I → Opens
S` satisfying `CoversTop U`, if `a.over (U i)=b.over (U i)` for every `i`, then `a=b`. All
four universes are independent. -/
theorem hom_ext_of_over_cover {S : Type u} [TopologicalSpace S]
    {R : Sheaf (_root_.Opens.grothendieckTopology S) RingCat.{v}}
    {M N : SheafOfModules.{w} R} (a b : M ⟶ N)
    {I : Type z} (U : I → _root_.TopologicalSpace.Opens S)
    (hU : (_root_.Opens.grothendieckTopology S).CoversTop U)
    (h : ∀ i, a.over (U i) = b.over (U i)) : a = b := by
  ext V m
  apply N.isSheaf.isSeparated _ _ (hU V.unop)
  intro W v hv
  obtain ⟨i, ⟨w⟩⟩ := (Sieve.mem_ofObjects_iff U v).mp hv
  have hh := congrArg (fun q : M.over (U i) ⟶ N.over (U i) =>
    q.val.app (op (Over.mk w)) (M.val.map v.op m)) (h i)
  change N.val.map v.op (a.val.app V m) = N.val.map v.op (b.val.app V m)
  exact (PresheafOfModules.naturality_apply a.val v.op m).symm.trans
    (hh.trans (PresheafOfModules.naturality_apply b.val v.op m))

end SheafOfModules
