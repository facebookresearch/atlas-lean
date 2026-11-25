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
# Gluing module sheaf morphisms and isomorphisms on an open cover

Local morphisms that agree on cover intersections glue uniquely.
When the local morphisms are isomorphisms, their inverses glue as well.
-/

@[expose] public section

set_option autoImplicit false

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
variable {ι : Type v} {U : ι → Opens X}
variable {F G : SheafOfModules.{u} R}

section CoverData

/-- Local Hom data on a cover: per-chart linear maps on every open below
the chart, natural in the open, agreeing on overlaps. This is the
section-level form of "morphisms `F|_{U i} ⟶ G|_{U i}` compatible on
overlaps", avoiding restriction functors (which pinned Mathlib cannot
compute at sections for `Scheme.Modules.pullback`). -/
structure CoverHomData (F G : SheafOfModules.{u} R) (U : ι → Opens X) where
  /-- The per-chart maps, on every open below the chart. -/
  localHom : ∀ (i : ι) (V : Opens X), (V ≤ U i) →
    (F.val.obj (op V) ⟶ G.val.obj (op V))
  /-- Naturality in the open, stated for an arbitrary inclusion morphism
  (so it applies to `infLELeft`/`infLERight` directly, with no
  inclusion-equality rewriting). -/
  naturality : ∀ (i : ι) (V W : Opens X) (hV : V ≤ U i) (f : W ⟶ V)
    (x : ↥(F.val.obj (op V))),
    (G.val.map f.op) (localHom i V hV x) =
      localHom i W ((leOfHom f).trans hV) ((F.val.map f.op) x)
  /-- Agreement on overlaps: on any open below both charts, the two maps
  coincide. This is the section-level content of the consumers' `agree`
  cocycles. -/
  agree : ∀ (i k : ι) (V : Opens X) (hVi : V ≤ U i) (hVk : V ≤ U k),
    localHom i V hVi = localHom k V hVk

/-- Local iso data on a cover: Hom data in both directions, inverse on
every covered open. Section-level inverse laws (rather than `≫ = 𝟙`) keep
the input elementary: consumers with genuine local isos supply
`Iso.hom_inv_id`/`Iso.inv_hom_id` pointwise. -/
structure CoverIsoData (F G : SheafOfModules.{u} R) (U : ι → Opens X) where
  /-- The forward local maps. -/
  fwd : CoverHomData F G U
  /-- The backward local maps. -/
  bwd : CoverHomData G F U
  /-- Left-inverse law on every covered open. -/
  left_inv : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i)
    (x : ↥(F.val.obj (op V))),
    bwd.localHom i V hV (fwd.localHom i V hV x) = x
  /-- Right-inverse law on every covered open. -/
  right_inv : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i)
    (y : ↥(G.val.obj (op V))),
    fwd.localHom i V hV (bwd.localHom i V hV y) = y

end CoverData

section CoverLemmas

variable (U)

/-- The trace of a cover on an open covers that open: `V ≤ ⨆ i, V ⊓ U i`.
Via carriers (`Opens.coe_iSup`, `Opens.mem_inf`) and
`IsOpenCover.exists_mem`, so no frame distributive law is needed. -/
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

/-- The target sheaf of modules as an `Ab`-valued sheaf, so the
section-gluing API applies. The first projection is definitionally
`G.val.presheaf` (anonymous-constructor iota), hence the `rfl` identifications
`targetSheafAb_obj`/`targetSheafAb_map` below. -/
noncomputable abbrev targetSheafAb :
    TopCat.Sheaf Ab X :=
  ⟨G.val.presheaf, G.isSheaf⟩

/-- Sections of the transported sheaf are the module sections,
definitionally (`PresheafOfModules.presheaf_obj_coe`). -/
theorem targetSheafAb_obj (V : Opens X) :
    (↥((targetSheafAb (R := R) G).1.obj (op V)) : Type _) =
      ↥(G.val.obj (op V)) :=
  rfl

/-- Restriction in the transported sheaf is the module restriction,
definitionally (`PresheafOfModules.presheaf_map_apply_coe`). -/
theorem targetSheafAb_map {A B : (Opens X)ᵒᵖ} (f : A ⟶ B)
    (t : ↥(G.val.obj A)) :
    ((targetSheafAb (R := R) G).1.map f) t = (G.val.map f) t :=
  rfl

end TargetSheaf

section Gluing

variable (D : CoverHomData F G U)

/-- The inclusion `V ⊓ U i ⟶ V` induced by the open cover. -/
noncomputable def traceIncl (U : ι → Opens X) (V : Opens X) (i : ι) :
    V ⊓ U i ⟶ V :=
  homOfLE inf_le_left

/-- The candidate glued family at an open: restrict the section to each
trace open, then apply the local map. -/
noncomputable def gluedFam (V : Opens X) (s : ↥(F.val.obj (op V)))
    (i : ι) : ↥(G.val.obj (op (V ⊓ U i))) :=
  D.localHom i (V ⊓ U i) inf_le_right
    ((F.val.map (traceIncl U V i).op) s)

/-- The candidate family is compatible, by local naturality (push the
outer restriction inside the local map on each side), restriction merging
(`map_comp_apply` + `Subsingleton.elim` on opens maps), and local
agreement. -/
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

/-- Existence of the glued section, stated in module terms. -/
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

/-- The glued value at an open: the chosen glued section. -/
noncomputable def gluedApp (hU : IsOpenCover U) (V : Opens X)
    (s : ↥(F.val.obj (op V))) : ↥(G.val.obj (op V)) :=
  (glueExists D hU V s).choose

/-- The glued value restricts to the local maps. -/
theorem gluedApp_spec (hU : IsOpenCover U) (V : Opens X)
    (s : ↥(F.val.obj (op V))) (i : ι) :
    (G.val.map (traceIncl U V i).op) (gluedApp D hU V s) =
      gluedFam D V s i :=
  (glueExists D hU V s).choose_spec i

/-- Locality for the target: two sections agreeing on every trace open
are equal (`eq_of_locally_eq'`). All Hom-level facts below (restriction,
additivity, linearity, naturality, uniqueness) go through this. -/
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

/-- The glued value on a covered open is the local map, by locality. -/
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

/-- The glued value preserves addition, by locality plus linearity of the
local maps and restriction maps. -/
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

/-- The glued value preserves scalar multiplication, by locality plus
linearity of the local maps and semilinearity of restriction
(`PresheafOfModules.map_smul`). -/
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

/-- The glued values are natural in the open, by locality: both sides
restrict (via restriction merging) to the local map applied to the
twice-restricted section. -/
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

/-- The glued presheaf morphism: bundle the glued values (additive and
linear by `gluedApp_add`/`gluedApp_smul`) with naturality
(`gluedApp_natural`, via `Subsingleton.elim` since opens maps are unique).
A morphism of sheaves of modules is a morphism of underlying presheaves,
so this already determines the sheaf morphism. -/
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

/-- The glued morphism restricts to the local maps on covered opens. -/
theorem glueCoverHom_restricts (hU : IsOpenCover U) (i : ι)
    (V : Opens X) (hV : V ≤ U i) :
    (glueCoverHom D hU).app (op V) = D.localHom i V hV := by
  ext x
  change gluedApp D hU V x = D.localHom i V hV x
  exact gluedApp_restricts D hU V x i hV

/-- Uniqueness: two sheaf morphisms agreeing on a cover are equal. By
`SheafOfModules.hom_ext` + `PresheafOfModules.hom_ext` it suffices to check
per-open, per-section, where both sides restrict (by naturality) to the
agreed values on the trace cover — closed by `locally_eq`. -/
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

/-- Amalgamation of overlap-compatible local data into a global iso: glue
hom and inv separately, then prove the inverse laws by uniqueness
(`coverHom_ext`), since they hold on the cover by `left_inv`/`right_inv`. -/
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

/-- The forward half of the glued iso restricts to the local maps. -/
theorem glueCoverIso_hom_restricts (hU : IsOpenCover U) (i : ι)
    (V : Opens X) (hV : V ≤ U i) :
    (glueCoverIso D hU).hom.val.app (op V) = D.fwd.localHom i V hV :=
  glueCoverHom_restricts D.fwd hU i V hV

/-- The backward half of the glued iso restricts to the local maps. -/
theorem glueCoverIso_inv_restricts (hU : IsOpenCover U) (i : ι)
    (V : Opens X) (hV : V ≤ U i) :
    (glueCoverIso D hU).inv.val.app (op V) = D.bwd.localHom i V hV :=
  glueCoverHom_restricts D.bwd hU i V hV

end IsoGluing


end
end SheafOfModules
