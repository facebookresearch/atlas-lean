/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

/-
Historical source credit

Retained source scope: the generic cover morphism and isomorphism gluing constructions.

Original source:
`FormalizedTextbooks/Hartshorne1977/AlgebraicGeometry/Differentials/GluedComparisonMorphism.lean`
Source commit: `80affa07d93acef16eef9348f383069336505fb3`.
Prior source credit, verbatim:
  "Author: Muse Code"

These entries record the retained source history.
The current file author is the leading entry above.
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sets.OpenCover
namespace SheafOfModules

/-!
# Gluing module-sheaf morphisms and isomorphisms on open covers

Let `X : TopCat.{u}`, `R` be a sheaf of rings of carrier universe `u`, and `F,G` be module
sheaves of carrier universe `u`. For a family `U : ι → Opens X` with `ι : Type v`, local
linear maps on all subopens of each `U_i`, natural under restriction and equal on common
subopens, form `CoverHomData`.

If `U` is an open cover, these maps glue to a unique natural module-presheaf morphism and
hence to a module-sheaf morphism. Local maps in both directions with pointwise inverse laws
form `CoverIsoData` and glue to a sheaf isomorphism. The construction computes the glued value
by sheaf gluing on the trace cover `V ∩ U_i` of each open `V`.
-/

@[expose] public section

set_option autoImplicit false

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
variable {ι : Type v} {U : ι → Opens X}
variable {F G : SheafOfModules.{u} R}

section CoverData

/-- Let `X : TopCat.{u}`, `R` be a ring sheaf of carrier universe `u`, `F,G` module sheaves of
carrier universe `u`, and `U : ι → Opens X` with `ι : Type v`. `CoverHomData F G U` consists
of `R(V)`-linear maps `F(V) → G(V)` for every chart `i` and `V ≤ U_i`, natural under
inclusions of subopens and equal whenever `V` lies below two charts. The fields are
`localHom`, `naturality`, and `agree`. -/
structure CoverHomData (F G : SheafOfModules.{u} R) (U : ι → Opens X) where
  /-- For module sheaves `F,G` over a ringed space `(X,R)` and a family `U_i` of opens, this field
assigns an `R(V)`-linear map `F(V) → G(V)` to each `i`, open `V`, and inclusion proof `V ≤
U_i`. The section modules are `F.val.obj (op V)` and `G.val.obj (op V)`. -/
  localHom : ∀ (i : ι) (V : Opens X), (V ≤ U i) →
    (F.val.obj (op V) ⟶ G.val.obj (op V))
  /-- Let `F,G` be module sheaves over a ringed space `(X,R)`, `U` a family of opens, and `D :
CoverHomData F G U`. This field requires that every inclusion `f : W → V` with `V ≤ U_i`
satisfy `G(f.op)(D.localHom i V x) = D.localHom i W (F(f.op)(x))` for every `x∈F(V)`. The
local map on `W` uses the induced inclusion `W ≤ U_i`. -/
  naturality : ∀ (i : ι) (V W : Opens X) (hV : V ≤ U i) (f : W ⟶ V)
    (x : ↥(F.val.obj (op V))),
    (G.val.map f.op) (localHom i V hV x) =
      localHom i W ((leOfHom f).trans hV) ((F.val.map f.op) x)
  /-- For module sheaves `F,G` over `(X,R)` and local morphism data on a family `U`, this field
requires `localHom i V h_i = localHom k V h_k` as `R(V)`-linear maps whenever `V ≤ U_i` and `V
≤ U_k`. Thus the local maps coincide on every common subopen. -/
  agree : ∀ (i k : ι) (V : Opens X) (hVi : V ≤ U i) (hVk : V ≤ U k),
    localHom i V hVi = localHom k V hVk

/-- For module sheaves `F,G` over a ringed space `(X,R)` and a family of opens `U_i`,
`CoverIsoData F G U` consists of compatible local morphism data `F → G` and `G → F`, with both
pointwise inverse laws on every `V ≤ U_i`. Its fields are `fwd`, `bwd`, `left_inv`, and
`right_inv`. -/
structure CoverIsoData (F G : SheafOfModules.{u} R) (U : ι → Opens X) where
  /-- For module sheaves `F,G` over `(X,R)` and a family `U`, this field of `CoverIsoData F G U` is
`CoverHomData F G U`: linear maps `F(V) → G(V)` for every `V ≤ U_i`, natural under restriction
and equal on common subopens. -/
  fwd : CoverHomData F G U
  /-- For module sheaves `F,G` over `(X,R)` and a family `U`, this field of `CoverIsoData F G U` is
`CoverHomData G F U`: linear maps `G(V) → F(V)` for every `V ≤ U_i`, natural under restriction
and equal on common subopens. -/
  bwd : CoverHomData G F U
  /-- Let `F,G` be module sheaves over a ringed space `(X,R)`, `U` a family of opens, and `D :
CoverIsoData F G U`. For every chart `i`, subopen `V ≤ U_i`, and `x∈F(V)`, `D.bwd.localHom i V
(D.fwd.localHom i V x)=x`. Thus the backward local map is a left inverse of the forward local
map on the source section module. -/
  left_inv : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i)
    (x : ↥(F.val.obj (op V))),
    bwd.localHom i V hV (fwd.localHom i V hV x) = x
  /-- Let `F,G` be module sheaves on a ringed space `(X,R)`, `U` a family of opens, and `D :
CoverIsoData F G U`. For every chart `i`, `V ≤ U_i`, and `y∈G(V)`, `D.fwd.localHom i V
(D.bwd.localHom i V y)=y`. Thus the forward local map is a left inverse of the backward local
map on each target section module. -/
  right_inv : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i)
    (y : ↥(G.val.obj (op V))),
    fwd.localHom i V hV (bwd.localHom i V hV y) = y

end CoverData

section CoverLemmas

variable (U)

/-- Let `X` be a topological space, `U : ι → Opens X` an open cover, and `V : Opens X`. Then `V ≤
⨆ i, V ⊓ U i`: every point of `V` lies in one of the trace opens `V ∩ U_i`. The index type `ι`
may have a universe independent of `X`. -/
theorem coverInter_le (V : Opens X) (hU : IsOpenCover U) :
    V ≤ ⨆ i, V ⊓ U i := by
  apply SetLike.coe_subset_coe.mp
  intro x hx
  rw [Opens.coe_iSup]
  obtain ⟨i, hi⟩ := hU.exists_mem x
  exact Set.mem_iUnion.mpr ⟨i, Opens.mem_inf.mpr ⟨hx, hi⟩⟩

end CoverLemmas

section TargetSheaf

variable (G)

/-- Let `X : TopCat.{u}`, `R` be a ring sheaf of carrier universe `u`, and `G : SheafOfModules.{u}
R`. The sheaf `targetSheafAb G : TopCat.Sheaf Ab X` has presheaf `G.val.presheaf` and the
sheaf condition supplied by `G`. It forgets the module scalar action while retaining the
additive sections and restrictions. -/
noncomputable abbrev targetSheafAb :
    TopCat.Sheaf Ab X :=
  ⟨G.val.presheaf, G.isSheaf⟩

/-- Let `G` be a module sheaf over a ring sheaf `R` on a space `X`, and `V∈Opens X`. The section
type of `targetSheafAb G` at `V` equals the underlying section type of `G.val.obj (op V)`.
Thus forgetting the module action leaves the same carrier of sections. -/
theorem targetSheafAb_obj (V : Opens X) :
    (↥((targetSheafAb (R := R) G).1.obj (op V)) : Type _) =
      ↥(G.val.obj (op V)) :=
  rfl

/-- Let `G` be a module sheaf over a ring sheaf `R` on `X`. For `f : A → B` in `(Opens X)ᵒᵖ` and
`t∈G.val.obj A`, `((targetSheafAb G).1.map f)(t) = (G.val.map f)(t)`. The underlying abelian
sheaf uses the same restriction map on each section. -/
theorem targetSheafAb_map {A B : (Opens X)ᵒᵖ} (f : A ⟶ B)
    (t : ↥(G.val.obj A)) :
    ((targetSheafAb (R := R) G).1.map f) t = (G.val.map f) t :=
  rfl

end TargetSheaf

section Gluing

variable (D : CoverHomData F G U)

/-- For a space `X`, a family `U : ι → Opens X`, `V : Opens X`, and `i∈ι`, `traceIncl U V i` is
the canonical inclusion `V ⊓ U i → V` induced by `V ∩ U_i ⊆ V`. -/
noncomputable def traceIncl (U : ι → Opens X) (V : Opens X) (i : ι) :
    V ⊓ U i ⟶ V :=
  homOfLE inf_le_left

/-- Let `F,G` be module sheaves over `(X,R)`, `U` a family of opens, and `D : CoverHomData F G U`.
For `V∈Opens X`, `s∈F(V)`, and `i∈ι`, `gluedFam D V s i` is the section of `G(V ∩ U_i)`
obtained by restricting `s` to that trace open and applying `D.localHom i (V ⊓ U i)
inf_le_right`. -/
noncomputable def gluedFam (V : Opens X) (s : ↥(F.val.obj (op V)))
    (i : ι) : ↥(G.val.obj (op (V ⊓ U i))) :=
  D.localHom i (V ⊓ U i) inf_le_right
    ((F.val.map (traceIncl U V i).op) s)

/-- Let `F,G` be module sheaves on `(X,R)` and `D : CoverHomData F G U`. For every open `V` and
section `s∈F(V)`, the family `i ↦ gluedFam D V s i` is compatible on the opens `V ∩ U_i`: its
two restrictions to any pairwise intersection agree. Compatibility follows from restriction
naturality and agreement of the local maps on common subopens. -/
theorem gluedFam_compat (V : Opens X) (s : ↥(F.val.obj (op V))) :
    TopCat.Presheaf.IsCompatible (targetSheafAb G).1 (fun i => V ⊓ U i)
      (fun i => (gluedFam D V s i :
        ToType ((targetSheafAb G).1.obj (op (V ⊓ U i))))) := by
  intro i j
  change (G.val.map (Opens.infLELeft (V ⊓ U i) (V ⊓ U j)).op)
      (gluedFam D V s i) =
    (G.val.map (Opens.infLERight (V ⊓ U i) (V ⊓ U j)).op)
      (gluedFam D V s j)
  have e1 := D.naturality i (V ⊓ U i) ((V ⊓ U i) ⊓ (V ⊓ U j))
    inf_le_right (Opens.infLELeft (V ⊓ U i) (V ⊓ U j))
    ((F.val.map (traceIncl U V i).op) s)
  have e2 := D.naturality j (V ⊓ U j) ((V ⊓ U i) ⊓ (V ⊓ U j))
    inf_le_right (Opens.infLERight (V ⊓ U i) (V ⊓ U j))
    ((F.val.map (traceIncl U V j).op) s)
  change (G.val.map (Opens.infLELeft (V ⊓ U i) (V ⊓ U j)).op)
      (D.localHom i (V ⊓ U i) inf_le_right
        ((F.val.map (traceIncl U V i).op) s)) =
    (G.val.map (Opens.infLERight (V ⊓ U i) (V ⊓ U j)).op)
      (D.localHom j (V ⊓ U j) inf_le_right
        ((F.val.map (traceIncl U V j).op) s))
  rw [e1, e2]
  have hF : (F.val.map (Opens.infLELeft (V ⊓ U i) (V ⊓ U j)).op)
        ((F.val.map (traceIncl U V i).op) s) =
      (F.val.map (Opens.infLERight (V ⊓ U i) (V ⊓ U j)).op)
        ((F.val.map (traceIncl U V j).op) s) := by
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) s
  rw [hF, D.agree i j ((V ⊓ U i) ⊓ (V ⊓ U j)) _ _]

/-- Let `F,G` be module sheaves over `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
every `V∈Opens X` and `s∈F(V)`, there exists `t∈G(V)` whose restriction to each `V ∩ U_i`
equals `gluedFam D V s i`, the image under the local map of the restriction of `s`. -/
theorem glueExists (hU : IsOpenCover U) (V : Opens X)
    (s : ↥(F.val.obj (op V))) :
    ∃ t : ↥(G.val.obj (op V)), ∀ i : ι,
      (G.val.map (traceIncl U V i).op) t = gluedFam D V s i := by
  obtain ⟨t, ht, -⟩ := (targetSheafAb G).existsUnique_gluing'
    (fun i => V ⊓ U i) V (fun i => traceIncl U V i)
    (coverInter_le U V hU)
    (fun i => (gluedFam D V s i :
      ToType ((targetSheafAb G).1.obj (op (V ⊓ U i)))))
    (gluedFam_compat D V s)
  refine ⟨(t : ↥(G.val.obj (op V))), fun i => ?_⟩
  exact ht i

/-- Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
`V∈Opens X` and `s∈F(V)`, `gluedApp D hU V s` is the section of `G(V)` whose restrictions to
`V ∩ U_i` are the local images `D.localHom i (V ∩ U_i)(s|_{V∩U_i})`. The target sheaf's
separatedness makes this section unique. -/
noncomputable def gluedApp (hU : IsOpenCover U) (V : Opens X)
    (s : ↥(F.val.obj (op V))) : ↥(G.val.obj (op V)) :=
  (glueExists D hU V s).choose

/-- Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
`V∈Opens X`, `s∈F(V)`, and each `i`, the restriction of `gluedApp D hU V s` along `V ∩ U_i →
V` equals `gluedFam D V s i`, the prescribed local image on that trace open. -/
theorem gluedApp_spec (hU : IsOpenCover U) (V : Opens X)
    (s : ↥(F.val.obj (op V))) (i : ι) :
    (G.val.map (traceIncl U V i).op) (gluedApp D hU V s) =
      gluedFam D V s i :=
  (glueExists D hU V s).choose_spec i

/-- Let `G` be a module sheaf on a ringed space `(X,R)`, `U` an open cover, and `V∈Opens X`. If
`a,b∈G(V)` have the same restriction to every trace open `V ∩ U_i`, then `a=b`. The equality
condition uses the canonical inclusions `traceIncl U V i`. -/
theorem locally_eq (hU : IsOpenCover U) (V : Opens X)
    (a b : ↥(G.val.obj (op V)))
    (h : ∀ i : ι, (G.val.map (traceIncl U V i).op) a =
      (G.val.map (traceIncl U V i).op) b) : a = b := by
  have h' : ∀ i : ι, ((targetSheafAb G).1.map (traceIncl U V i).op)
      (a : ToType ((targetSheafAb G).1.obj (op V))) =
      ((targetSheafAb G).1.map (traceIncl U V i).op)
      (b : ToType ((targetSheafAb G).1.obj (op V))) :=
    fun i => h i
  exact (targetSheafAb G).eq_of_locally_eq' (fun i => V ⊓ U i) V
    (fun i => traceIncl U V i) (coverInter_le U V hU) _ _ h'

/-- Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. If `V
≤ U_j`, then for every `s∈F(V)`, `gluedApp D hU V s = D.localHom j V hV s`. Thus the glued
value is the prescribed local value on any subopen of a chart. -/
theorem gluedApp_restricts (hU : IsOpenCover U) (V : Opens X)
    (s : ↥(F.val.obj (op V))) (j : ι) (hV : V ≤ U j) :
    gluedApp D hU V s = D.localHom j V hV s := by
  apply locally_eq hU V
  intro i
  have eL := gluedApp_spec D hU V s i
  change (G.val.map (traceIncl U V i).op) (gluedApp D hU V s) =
    (G.val.map (traceIncl U V i).op) (D.localHom j V hV s)
  rw [eL, D.naturality j V _ hV (traceIncl U V i) s]
  change D.localHom i (V ⊓ U i) inf_le_right
      ((F.val.map (traceIncl U V i).op) s) =
    D.localHom j (V ⊓ U i) _ ((F.val.map (traceIncl U V i).op) s)
  rw [D.agree i j (V ⊓ U i) _ _]

/-- Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
`V∈Opens X` and `s,t∈F(V)`, `gluedApp D hU V (s+t) = gluedApp D hU V s + gluedApp D hU V t` in
`G(V)`. -/
theorem gluedApp_add (hU : IsOpenCover U) (V : Opens X)
    (s t : ↥(F.val.obj (op V))) :
    gluedApp D hU V (s + t) =
      gluedApp D hU V s + gluedApp D hU V t := by
  apply locally_eq hU V
  intro i
  have e1 := gluedApp_spec D hU V (s + t) i
  have e2 := gluedApp_spec D hU V s i
  have e3 := gluedApp_spec D hU V t i
  have e2h : ((G.val.map (traceIncl U V i).op).hom)
      (gluedApp D hU V s) = gluedFam D V s i := e2
  have e3h : ((G.val.map (traceIncl U V i).op).hom)
      (gluedApp D hU V t) = gluedFam D V t i := e3
  rw [e1]
  change ((D.localHom i (V ⊓ U i) inf_le_right).hom)
      (((F.val.map (traceIncl U V i).op).hom) (s + t)) =
    ((G.val.map (traceIncl U V i).op).hom)
      (gluedApp D hU V s + gluedApp D hU V t)
  rw [map_add ((G.val.map (traceIncl U V i).op).hom)
    (gluedApp D hU V s) (gluedApp D hU V t), e2h, e3h]
  change ((D.localHom i (V ⊓ U i) inf_le_right).hom)
      (((F.val.map (traceIncl U V i).op).hom) (s + t)) =
    ((D.localHom i (V ⊓ U i) inf_le_right).hom)
      (((F.val.map (traceIncl U V i).op).hom) s) +
    ((D.localHom i (V ⊓ U i) inf_le_right).hom)
      (((F.val.map (traceIncl U V i).op).hom) t)
  rw [map_add (((F.val.map (traceIncl U V i).op).hom)) s t]
  exact map_add ((D.localHom i (V ⊓ U i) inf_le_right).hom) _ _

/-- Let `F,G` be module sheaves over a ring sheaf `R` on `X`, `U` an open cover, and `D :
CoverHomData F G U`. For `V∈Opens X`, `r∈R(V)`, and `s∈F(V)`, `gluedApp D hU V (r • s) = r •
gluedApp D hU V s`, using the left module structures over `R(V)`. -/
theorem gluedApp_smul (hU : IsOpenCover U) (V : Opens X)
    (r : R.obj.obj (op V)) (s : ↥(F.val.obj (op V))) :
    gluedApp D hU V (r • s) = r • gluedApp D hU V s := by
  apply locally_eq hU V
  intro i
  have e1 := gluedApp_spec D hU V (r • s) i
  have e2 := gluedApp_spec D hU V s i
  have smulG : ((G.val.map (traceIncl U V i).op).hom)
      (r • gluedApp D hU V s) =
      (R.obj.map (traceIncl U V i).op) r •
        ((G.val.map (traceIncl U V i).op).hom) (gluedApp D hU V s) :=
    PresheafOfModules.map_smul (G.val) ((traceIncl U V i).op) r
      (gluedApp D hU V s)
  have e2h : ((G.val.map (traceIncl U V i).op).hom)
      (gluedApp D hU V s) = gluedFam D V s i := e2
  have smulF : (((F.val.map (traceIncl U V i).op).hom)) (r • s) =
      (R.obj.map (traceIncl U V i).op) r •
        (((F.val.map (traceIncl U V i).op).hom)) s :=
    PresheafOfModules.map_smul (F.val) ((traceIncl U V i).op) r s
  rw [e1]
  change ((D.localHom i (V ⊓ U i) inf_le_right).hom)
      (((F.val.map (traceIncl U V i).op).hom) (r • s)) =
    ((G.val.map (traceIncl U V i).op).hom) (r • gluedApp D hU V s)
  rw [smulG, e2h]
  change ((D.localHom i (V ⊓ U i) inf_le_right).hom)
      (((F.val.map (traceIncl U V i).op).hom) (r • s)) =
    (R.obj.map (traceIncl U V i).op) r •
      ((D.localHom i (V ⊓ U i) inf_le_right).hom)
        (((F.val.map (traceIncl U V i).op).hom) s)
  rw [smulF]
  exact map_smul ((D.localHom i (V ⊓ U i) inf_le_right).hom) _ _

/-- Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
an inclusion `h : W ≤ V` and `s∈F(V)`, `gluedApp D hU W (s|_W) = (gluedApp D hU V s)|_W`. The
restrictions are the presheaf maps along `(homOfLE h).op`. -/
theorem gluedApp_natural (hU : IsOpenCover U) (V W : Opens X)
    (h : W ≤ V) (s : ↥(F.val.obj (op V))) :
    gluedApp D hU W ((F.val.map (homOfLE h).op) s) =
      (G.val.map (homOfLE h).op) (gluedApp D hU V s) := by
  apply locally_eq hU W
  intro i
  have eL := gluedApp_spec D hU W ((F.val.map (homOfLE h).op) s) i
  have eR := gluedApp_spec D hU V s i
  have hWVi : W ⊓ U i ≤ V ⊓ U i := inf_le_inf h le_rfl
  have mergeG : (G.val.map (traceIncl U W i).op)
        ((G.val.map (homOfLE h).op) (gluedApp D hU V s)) =
      (G.val.map (homOfLE hWVi).op)
        ((G.val.map (traceIncl U V i).op)
          (gluedApp D hU V s)) := by
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _
  have hF : (((F.val.map (traceIncl U W i).op).hom)
        (((F.val.map (homOfLE h).op).hom) s)) =
      (((F.val.map (homOfLE hWVi).op).hom)
        (((F.val.map (traceIncl U V i).op).hom) s)) := by
    change (F.val.map (traceIncl U W i).op)
        ((F.val.map (homOfLE h).op) s) =
      (F.val.map (homOfLE hWVi).op)
        ((F.val.map (traceIncl U V i).op) s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) s
  have eN : (((G.val.map (homOfLE hWVi).op).hom)
        ((D.localHom i (V ⊓ U i) inf_le_right).hom
          (((F.val.map (traceIncl U V i).op).hom) s))) =
      (((D.localHom i (W ⊓ U i) _).hom)
        (((F.val.map (homOfLE hWVi).op).hom)
          (((F.val.map (traceIncl U V i).op).hom) s))) :=
    D.naturality i _ _ _ (homOfLE hWVi) _
  change (G.val.map (traceIncl U W i).op)
      (gluedApp D hU W ((F.val.map (homOfLE h).op) s)) =
    (G.val.map (traceIncl U W i).op)
      ((G.val.map (homOfLE h).op) (gluedApp D hU V s))
  rw [eL, mergeG, eR]
  change ((D.localHom i (W ⊓ U i) _).hom)
      (((F.val.map (traceIncl U W i).op).hom)
        (((F.val.map (homOfLE h).op).hom) s)) =
    ((G.val.map (homOfLE hWVi).op).hom)
      ((D.localHom i (V ⊓ U i) inf_le_right).hom
        (((F.val.map (traceIncl U V i).op).hom) s))
  rw [eN, hF]

end Gluing

section Assembly

variable (D : CoverHomData F G U)

/-- Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. The
morphism `glueCoverHom D hU : F.val → G.val` has component at `V` the `R(V)`-linear map `s ↦
gluedApp D hU V s`. These components commute with restrictions, so the presheaf morphism
determines a module-sheaf morphism. -/
noncomputable def glueCoverHom (hU : IsOpenCover U) : F.val ⟶ G.val where
  app X :=
    let lin : ↥(F.val.obj X) →ₗ[↥(R.obj.obj X)] ↥(G.val.obj X) :=
      { toFun := gluedApp D hU X.unop
        map_add' := fun x y => gluedApp_add D hU X.unop x y
        map_smul' := fun r x => gluedApp_smul D hU X.unop r x }
    ModuleCat.ofHom lin
  naturality {X Y} f := by
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [hf]
    ext x
    simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
    exact gluedApp_natural D hU _ _ _ x

/-- Let `F,G` be module sheaves over `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
any `i`, open `V`, and `hV : V ≤ U_i`, `(glueCoverHom D hU).app (op V) = D.localHom i V hV` as
`R(V)`-linear maps `F(V) → G(V)`. -/
theorem glueCoverHom_restricts (hU : IsOpenCover U) (i : ι)
    (V : Opens X) (hV : V ≤ U i) :
    (glueCoverHom D hU).app (op V) = D.localHom i V hV := by
  ext x
  change gluedApp D hU V x = D.localHom i V hV x
  exact gluedApp_restricts D hU V x i hV

/-- Let `F,G` be module sheaves over `(X,R)` and `U` an open cover. If `ψ₁,ψ₂ : F → G` have equal
component maps `F(V) → G(V)` for every chart `i` and every open `V ≤ U_i`, then `ψ₁=ψ₂` as
module-sheaf morphisms. -/
theorem coverHom_ext (hU : IsOpenCover U) (ψ₁ ψ₂ : F ⟶ G)
    (h : ∀ (i : ι) (V : Opens X) (_ : V ≤ U i),
      ψ₁.val.app (op V) = ψ₂.val.app (op V)) :
    ψ₁ = ψ₂ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Xo
  obtain ⟨V, rfl⟩ : ∃ V : Opens X, op V = Xo :=
    ⟨Xo.unop, (Opposite.op_unop Xo).symm⟩
  ext x
  apply locally_eq (R := R) (G := G) hU V
  intro i
  change (G.val.map (traceIncl U V i).op) ((ψ₁.val.app (op V)) x) =
    (G.val.map (traceIncl U V i).op) ((ψ₂.val.app (op V)) x)
  rw [← PresheafOfModules.naturality_apply ψ₁.val (traceIncl U V i).op x,
    ← PresheafOfModules.naturality_apply ψ₂.val (traceIncl U V i).op x]
  change (ψ₁.val.app (op (V ⊓ U i))).hom _ =
    (ψ₂.val.app (op (V ⊓ U i))).hom _
  exact DFunLike.congr_fun
    (congrArg (·.hom) (h i (V ⊓ U i) inf_le_right)) _

end Assembly

section IsoGluing

variable (D : CoverIsoData F G U)

/-- Let `F,G` be module sheaves over `(X,R)`, `U` an open cover, and `D : CoverIsoData F G U`
compatible local maps in both directions with the two pointwise inverse laws. Then
`glueCoverIso D hU : F ≅ G` has forward morphism determined by `glueCoverHom D.fwd hU` and
inverse morphism determined by `glueCoverHom D.bwd hU`. -/
noncomputable def glueCoverIso (hU : IsOpenCover U) : F ≅ G where
  hom := ⟨glueCoverHom D.fwd hU⟩
  inv := ⟨glueCoverHom D.bwd hU⟩
  hom_inv_id := by
    have h : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i),
        (⟨glueCoverHom D.fwd hU⟩ ≫ ⟨glueCoverHom D.bwd hU⟩ :
          F ⟶ F).val.app (op V) =
          PresheafOfModules.Hom.app (𝟙 F.val) (op V) := by
      intro i V hV
      change (glueCoverHom D.fwd hU).app (op V) ≫
          (glueCoverHom D.bwd hU).app (op V) = 𝟙 _
      ext x
      rw [ModuleCat.comp_apply]
      change (glueCoverHom D.bwd hU).app (op V)
          ((glueCoverHom D.fwd hU).app (op V) x) = x
      rw [glueCoverHom_restricts D.fwd hU i V hV,
        glueCoverHom_restricts D.bwd hU i V hV]
      exact D.left_inv i V hV x
    exact coverHom_ext hU _ _ h
  inv_hom_id := by
    have h : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i),
        (⟨glueCoverHom D.bwd hU⟩ ≫ ⟨glueCoverHom D.fwd hU⟩ :
          G ⟶ G).val.app (op V) =
          PresheafOfModules.Hom.app (𝟙 G.val) (op V) := by
      intro i V hV
      change (glueCoverHom D.bwd hU).app (op V) ≫
          (glueCoverHom D.fwd hU).app (op V) = 𝟙 _
      ext x
      rw [ModuleCat.comp_apply]
      change (glueCoverHom D.fwd hU).app (op V)
          ((glueCoverHom D.bwd hU).app (op V) x) = x
      rw [glueCoverHom_restricts D.bwd hU i V hV,
        glueCoverHom_restricts D.fwd hU i V hV]
      exact D.right_inv i V hV x
    exact coverHom_ext hU _ _ h

/-- Let `F,G` be module sheaves over `(X,R)`, `U` an open cover, and `D : CoverIsoData F G U`. For
every `i` and `V ≤ U_i`, `(glueCoverIso D hU).hom.val.app (op V) = D.fwd.localHom i V hV`.
Thus the global forward isomorphism has the prescribed local forward component. -/
theorem glueCoverIso_hom_restricts (hU : IsOpenCover U) (i : ι)
    (V : Opens X) (hV : V ≤ U i) :
    (glueCoverIso D hU).hom.val.app (op V) = D.fwd.localHom i V hV :=
  glueCoverHom_restricts D.fwd hU i V hV

/-- Let `F,G` be module sheaves over `(X,R)`, `U` an open cover, and `D : CoverIsoData F G U`. For
every `i` and `V ≤ U_i`, `(glueCoverIso D hU).inv.val.app (op V) = D.bwd.localHom i V hV`.
Thus the global inverse has the prescribed local backward component. -/
theorem glueCoverIso_inv_restricts (hU : IsOpenCover U) (i : ι)
    (V : Opens X) (hV : V ≤ U i) :
    (glueCoverIso D hU).inv.val.app (op V) = D.bwd.localHom i V hV :=
  glueCoverHom_restricts D.bwd hU i V hV

end IsoGluing


end
end SheafOfModules
