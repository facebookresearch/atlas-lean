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

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# A directed submodule supremum is its categorical union colimit

Let R be a ring, M an R-module and I a nonempty directed preorder.
For a monotone family S_i⊆M, the inclusions S_i→S_j, i≤j, form
a module diagram. Its supremum ⨆_i S_i is the directed union
and is the colimit in the carrier world of M.

A compatible family of linear maps out of the stages extends uniquely
to the supremum, retaining its value on every represented stage
element. The colimit also holds after forgetting the module structure.
The scalar, carrier and index worlds u,v,w are independent, and
the index world need not be bounded by the carrier world.

A linear map f:M→N with f(S_i)⊆T_i induces the corresponding
map on the suprema. When both families are monotone, its stage
maps form a diagram morphism and commute with the colimit legs.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat.DirectedSubmoduleColimit

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {ι : Type w} [Preorder ι]

/-- For a ring R, an R-module M and a monotone family
S:I→Submodule_R(M) on a preorder I, the diagram sends i to S_i
and i≤j to the submodule inclusion S_i→S_j.
Its objects have the carrier world v of M. -/
def diagram (S : ι → Submodule R M) (hS : Monotone S) : ι ⥤ ModuleCat.{v} R where
  obj i := ModuleCat.of R (S i)
  map f := ModuleCat.ofHom (Submodule.inclusion (hS (leOfHom f)))
  map_id i := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- For a monotone submodule family S_i⊆M, the inclusions
S_i→⨆_j S_j give a cocone on its module diagram.
Each map is the inclusion into the supremum inside M. -/
def cocone (S : ι → Submodule R M) (hS : Monotone S) : Cocone (diagram S hS) where
  pt := ModuleCat.of R ↥(⨆ i, S i : Submodule R M)
  ι :=
    { app i := ModuleCat.ofHom (Submodule.inclusion (le_iSup S i))
      naturality i j f := by
        apply ModuleCat.hom_ext
        ext x
        rfl }

/-- For a monotone submodule family S_i⊆M and x∈S_i,
the cocone leg to ⨆_j S_j has underlying value x in M.
Only its submodule-membership proof changes. -/
lemma inclusion_val (S : ι → Submodule R M) (hS : Monotone S) (i : ι) (x : S i) :
    (((cocone S hS).ι.app i).hom x).val = x.val := rfl

section Directed

variable [Nonempty ι] [IsDirectedOrder ι]

/-- For a monotone family S_i⊆M on a nonempty directed
preorder I, the supremum cocone is colimiting after forgetting
to the underlying carrier types.
Every element of the supremum is represented at some stage,
even when the index world exceeds the carrier world. -/
def typesIsColimit (S : ι → Submodule R M) (hS : Monotone S) :
    IsColimit ((forget (ModuleCat.{v} R)).mapCocone (cocone S hS)) := by
  refine Types.FilteredColimit.isColimitOf'
    (J := ι) (F := diagram S hS ⋙ forget (ModuleCat.{v} R))
    (t := (forget (ModuleCat.{v} R)).mapCocone (cocone S hS)) ?_ ?_
  · intro x
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    exact ⟨i, ⟨x.val, hx⟩, rfl⟩
  · intro i x y h
    change (Submodule.inclusion (le_iSup S i) x : ↥(⨆ j, S j : Submodule R M)) =
      (Submodule.inclusion (le_iSup S i) y : ↥(⨆ j, S j : Submodule R M)) at h
    have hv : x.val = y.val :=
      congrArg (fun z : ↥(⨆ j, S j : Submodule R M) => z.val) h
    have he : x = y := Subtype.ext hv
    exact ⟨i, 𝟙 i, congrArg
      (fun z => ((diagram S hS ⋙ forget (ModuleCat.{v} R)).map (𝟙 i)) z) he⟩

/-- For a monotone family S_i⊆M on a nonempty directed
preorder and a module cocone s, the universal function
⨆_i S_i→s.pt sends a stage representative x∈S_i to s_i(x).
Compatibility of the cocone makes this value independent
of the chosen stage. -/
def descFunction (S : ι → Submodule R M) (hS : Monotone S)
    (s : Cocone (diagram S hS)) : ↥(⨆ i, S i : Submodule R M) → s.pt :=
  (typesIsColimit S hS).desc ((forget (ModuleCat.{v} R)).mapCocone s)

/-- For a monotone directed nonempty submodule family S_i,
a cocone s and x∈S_i, the universal union function satisfies
desc(inclusion_i(x))=s_i(x).
It retains each prescribed stage value. -/
lemma descFunction_inclusion (S : ι → Submodule R M) (hS : Monotone S)
    (s : Cocone (diagram S hS)) (i : ι) (x : S i) :
    descFunction S hS s (Submodule.inclusion (le_iSup S i) x) = (s.ι.app i).hom x :=
  congrArg (fun f => f x) ((typesIsColimit S hS).fac
    ((forget (ModuleCat.{v} R)).mapCocone s) i)

/-- For a monotone family S_i⊆M over a nonempty directed
preorder and an R-linear cocone s, the universal map
⨆_i S_i→s.pt is R-linear.
Common upper stages preserve sums and scalar multiples. -/
def descLinear (S : ι → Submodule R M) (hS : Monotone S)
    (s : Cocone (diagram S hS)) : ↥(⨆ i, S i : Submodule R M) →ₗ[R] s.pt where
  toFun := descFunction S hS s
  map_add' x y := by
    obtain ⟨i, xi, yi, hx, hy⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (typesIsColimit S hS) x y
    have hx' : Submodule.inclusion (le_iSup S i) xi = x := hx
    have hy' : Submodule.inclusion (le_iSup S i) yi = y := hy
    rw [← hx', ← hy']
    let k := Submodule.inclusion (le_iSup S i)
    calc
      descFunction S hS s (k xi + k yi) = descFunction S hS s (k (xi + yi)) :=
        congrArg (descFunction S hS s) (map_add k xi yi).symm
      _ = (s.ι.app i).hom (xi + yi) := descFunction_inclusion S hS s i _
      _ = (s.ι.app i).hom xi + (s.ι.app i).hom yi := map_add _ _ _
      _ = descFunction S hS s (k xi) + descFunction S hS s (k yi) :=
        congrArg₂ (fun a b : s.pt => a + b)
          (descFunction_inclusion S hS s i xi).symm
          (descFunction_inclusion S hS s i yi).symm
  map_smul' r x := by
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    let xi : S i := ⟨x.val, hx⟩
    let k := Submodule.inclusion (le_iSup S i)
    have he : k xi = x := Subtype.ext rfl
    rw [← he]
    calc
      descFunction S hS s (r • k xi) = descFunction S hS s (k (r • xi)) :=
        congrArg (descFunction S hS s) (map_smul k r xi).symm
      _ = (s.ι.app i).hom (r • xi) := descFunction_inclusion S hS s i _
      _ = r • (s.ι.app i).hom xi := map_smul _ _ _
      _ = r • descFunction S hS s (k xi) :=
        congrArg (fun y => r • y) (descFunction_inclusion S hS s i xi).symm

/-- For a ring R and a monotone submodule family S_i⊆M
on a nonempty directed preorder, the inclusion cocone with
point ⨆_i S_i is a colimit in ModuleCat^v(R).
Its universal map is the linear descent of the stage maps. -/
def isColimit (S : ι → Submodule R M) (hS : Monotone S) : IsColimit (cocone S hS) where
  desc s := ModuleCat.ofHom (descLinear S hS s)
  fac s i := by
    apply ModuleCat.hom_ext
    ext x
    exact descFunction_inclusion S hS s i x
  uniq s m hm := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    let xi : S i := ⟨x.val, hx⟩
    have he : Submodule.inclusion (le_iSup S i) xi = x := Subtype.ext rfl
    rw [← he]
    have h := congrArg (fun f : ModuleCat.of R (S i) ⟶ s.pt => f.hom xi) (hm i)
    exact h.trans (descFunction_inclusion S hS s i xi).symm

/-- For a monotone submodule family S_i⊆M on a nonempty
directed preorder I, the inclusion diagram has a colimit,
namely its supremum submodule inside M.
This is existence for that diagram, with independent scalar,
index and carrier worlds. -/
instance hasColimit (S : ι → Submodule R M) (hS : Monotone S) :
    HasColimit (diagram S hS) := ⟨_, isColimit S hS⟩

section Coefficients

variable {N : Type v} [AddCommGroup N] [Module R N]

/-- For submodule families S_i⊆M,T_i⊆N and an R-linear
map f:M→N with f(S_i)⊆T_i, restriction gives S_i→ₗ[R]T_i.
Its underlying function is f on each stage element. -/
def stageMap (S : ι → Submodule R M) (T : ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : ∀ i x, x ∈ S i → f x ∈ T i) (i : ι) : S i →ₗ[R] T i :=
  (f.domRestrict (S i)).codRestrict (T i) (fun x => hf i x.val x.property)

/-- For a monotone directed nonempty family S_i⊆M,
an arbitrary family T_i⊆N and an R-linear map f with
f(S_i)⊆T_i, there is an R-linear map
⨆_i S_i→⨆_i T_i with underlying value f(x).
The target family need not be assumed monotone for this map. -/
def iSupMap (S : ι → Submodule R M) (hS : Monotone S) (T : ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : ∀ i x, x ∈ S i → f x ∈ T i) :
    ↥(⨆ i, S i : Submodule R M) →ₗ[R] ↥(⨆ i, T i : Submodule R N) :=
  (f.domRestrict (⨆ i, S i : Submodule R M)).codRestrict (⨆ i, T i : Submodule R N) (fun x => by
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    exact Submodule.mem_iSup_of_mem i (hf i x.val hx))

/-- For a stage-preserving R-linear map f:M→N, the induced
map ⨆_i S_i→⨆_i T_i sends an element represented by x∈M
to the element represented by f(x)∈N.
The source family is monotone on a nonempty directed preorder. -/
lemma iSupMap_val (S : ι → Submodule R M) (hS : Monotone S) (T : ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : ∀ i x, x ∈ S i → f x ∈ T i) (x : ↥(⨆ i, S i : Submodule R M)) :
    (iSupMap S hS T f hf x).val = f x.val := rfl

/-- For monotone submodule families S_i⊆M,T_i⊆N and
an R-linear f with f(S_i)⊆T_i, its restrictions S_i→T_i
commute with every inclusion i≤j.
They define a natural transformation of the two module diagrams. -/
def coefficientDiagramMap (S : ι → Submodule R M) (hS : Monotone S)
    (T : ι → Submodule R N) (hT : Monotone T) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ S i → f x ∈ T i) : diagram S hS ⟶ diagram T hT where
  app i := ModuleCat.ofHom (stageMap S T f hf i)
  naturality i j g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- For monotone directed nonempty families S_i,T_i and
an R-linear map f preserving each stage, the square
S_i→⨆S and T_i→⨆T commutes with f|_(S_i) and the
induced supremum map. Both paths have underlying value f(x). -/
lemma inclusion_coefficient (S : ι → Submodule R M) (hS : Monotone S)
    (T : ι → Submodule R N) (hT : Monotone T) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ S i → f x ∈ T i) (i : ι) :
    (cocone S hS).ι.app i ≫ ModuleCat.ofHom (iSupMap S hS T f hf) =
      (coefficientDiagramMap S hS T hT f hf).app i ≫ (cocone T hT).ι.app i := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- For monotone directed nonempty submodule families
S_i⊆M,T_i⊆N and a stage-preserving R-linear f, universal
descent of the T-cocone precomposed with the restricted
stage maps equals the induced map ⨆S→⨆T. -/
lemma desc_coefficient (S : ι → Submodule R M) (hS : Monotone S)
    (T : ι → Submodule R N) (hT : Monotone T) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ S i → f x ∈ T i) :
    (isColimit S hS).desc ((Cocone.precompose
      (coefficientDiagramMap S hS T hT f hf)).obj (cocone T hT)) =
        ModuleCat.ofHom (iSupMap S hS T f hf) := by
  apply (isColimit S hS).hom_ext
  intro i
  exact ((isColimit S hS).fac _ i).trans
    (inclusion_coefficient S hS T hT f hf i).symm

end Coefficients
end Directed
end ModuleCat.DirectedSubmoduleColimit
