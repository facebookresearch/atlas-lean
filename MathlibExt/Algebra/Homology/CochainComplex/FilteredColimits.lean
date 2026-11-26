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

public import MathlibExt.Algebra.Category.ModuleCat.ColimitRanges
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite data in filtered colimits of module cochain complexes

Let R be a commutative ring, and consider integer-indexed cochain complexes
of R-modules. In a filtered colimit, finitely generated homogeneous images
in finitely many degrees lie in one common stage. Elements from the same
stage that agree in the colimit agree after a transition; the same holds
for cochain maps from a complex supported in finitely many degrees with
finitely generated terms.

If each nonzero term of the source has a specified finite R-basis, every
cochain map to a filtered colimit factors through one stage. Over a field,
finite-dimensional terms supply these bases. The common-stage image theorem
allows an independently sized filtered indexing category and assumes its
colimits exist in the module category; the element, equality and factorization
theorems use a small filtered category in the universe of the modules.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u v w

section DegreeImages

variable {R : Type u} [CommRing R]
variable {J : Type w} [Category.{v} J] [IsFiltered J]
variable {E : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} {c : Cocone E}
  {A : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Let R be a commutative ring, J a filtered category, and c a colimit cocone
of a diagram E of integer-indexed R-module cochain complexes. Assume
J-shaped colimits exist in the module category. For a map f:A → c.pt and
a finite set S of degrees, if each image im(fₙ) for n∈S is finitely
generated, then some j in J satisfies
im(fₙ) ⊆ im(cⱼⁿ:Eⱼⁿ → c.ptⁿ) for every n∈S.
The indexing category may have independent object and morphism universes. -/
theorem exists_stage_range_le_of_finite_degree_images [HasColimitsOfShape J (ModuleCat.{u} R)]
    (hc : IsColimit c) (f : A ⟶ c.pt) (S : Finset ℤ)
    (hfinite : ∀ n ∈ S, (LinearMap.range (f.f n).hom).FG) :
    ∃ j, ∀ n ∈ S, LinearMap.range (f.f n).hom ≤ LinearMap.range ((c.ι.app j).f n).hom := by
  classical
  let P (n : ℤ) (j : J) := LinearMap.range ((c.ι.app j).f n).hom
  have htop (n : ℤ) : (⨆ j : J, P n j) = (⊤ : Submodule R (c.pt.X n)) := by
    let F := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n
    let t : Cocone (E ⋙ F) := F.mapCocone c
    let ht : IsColimit t := isColimitOfPreserves F hc
    change (⨆ j, LinearMap.range (ModuleCat.colimitLegLinearMap t j)) = ⊤
    exact ModuleCat.IsColimit.iSup_range_eq_top (c := t) ht
  have hstage (n : S) : ∃ t : Finset J, LinearMap.range (f.f n).hom ≤ ⨆ j ∈ t, P n j := by
    apply ((Submodule.fg_iff_compact _).mp (hfinite n n.property)).exists_finset_of_le_iSup
    rw [htop]
    exact le_top
  choose T hT using hstage
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (S.attach.biUnion T)
  refine ⟨j, fun n hn => (hT ⟨n, hn⟩).trans ?_⟩
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  let a : k ⟶ j := (hj (Finset.mem_biUnion.mpr ⟨⟨n, hn⟩, Finset.mem_attach _ _, hk⟩)).some
  rintro _ ⟨x, rfl⟩
  exact ⟨((E.map a).f n).hom x, congrArg (fun g => (g.f n).hom x) (c.w a)⟩

end DegreeImages

section Equality

variable {R : Type u} [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {E : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} {t : Cocone E}

/-- Let R be a commutative ring and t a colimit cocone for a diagram E of
integer-indexed R-module cochain complexes over a small filtered category J
in the universe of the modules. If x,y∈Eᵢⁿ have the same image in t.ptⁿ,
there is an arrow a:i → j such that E(a)ₙ(x)=E(a)ₙ(y). -/
theorem exists_stage_eq_of_filtered_colimit_element (ht : IsColimit t) {i : J} {n : ℤ}
    (x y : (E.obj i).X n)
    (h : ((t.ι.app i).f n).hom x = ((t.ι.app i).f n).hom y) :
    ∃ (j : J) (a : i ⟶ j), ((E.map a).f n).hom x = ((E.map a).f n).hom y := by
  let F := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n ⋙ forget (ModuleCat.{u} R)
  let c : Cocone (E ⋙ F) := F.mapCocone t
  let hc : IsColimit c := isColimitOfPreserves F ht
  exact (Types.FilteredColimit.isColimit_eq_iff' hc x y).mp h

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring and t a colimit cocone of module cochain
complexes over a small filtered category J in the universe of the modules.
Let A vanish outside a finite set S of integer degrees and have finitely
generated R-module terms in S. If two cochain maps p,q:A → Eᵢ have equal
composites into t.pt, then some arrow a:i → j makes
E(a) ∘ p = E(a) ∘ q as cochain maps. -/
theorem exists_stage_eq_of_filtered_colimit_finite_support (ht : IsColimit t) {i : J}
    {A : CochainComplex (ModuleCat.{u} R) ℤ} (p q : A ⟶ E.obj i) (S : Finset ℤ)
    (hfinite : ∀ n ∈ S, Module.Finite R (A.X n)) (hzero : ∀ n ∉ S, IsZero (A.X n))
    (h : p ≫ t.ι.app i = q ≫ t.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), p ≫ E.map a = q ≫ E.map a := by
  classical
  have hgen (n : S) : ∃ B : Finset (A.X n), Submodule.span R (B : Set (A.X n)) = ⊤ :=
    (hfinite n n.property).fg_top
  choose B hB using hgen
  let I := Σ n : S, ↥(B n)
  let : Finite I := inferInstanceAs (Finite (Σ n : S, ↥(B n)))
  have hpoint (d : I) : ∃ (j : J) (a : i ⟶ j),
      ((E.map a).f d.1).hom ((p.f d.1).hom d.2) =
        ((E.map a).f d.1).hom ((q.f d.1).hom d.2) :=
    exists_stage_eq_of_filtered_colimit_element ht _ _
      (congrArg (fun f => (f.f d.1).hom d.2) h)
  choose j b hb using hpoint
  obtain ⟨k, a, g, hg⟩ := IsFiltered.wideSpan b
  refine ⟨k, a, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n ∈ S
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let m : S := ⟨n, hn⟩
    have hx : x ∈ Submodule.span R (B m : Set (A.X n)) := by
      rw [hB m]
      exact Submodule.mem_top
    apply LinearMap.eqOn_span (s := (B m : Set (A.X n))) ?_ hx
    intro y hy
    let d : I := ⟨m, ⟨y, hy⟩⟩
    have ha : E.map a = E.map (b d) ≫ E.map (g d) := by
      rw [← E.map_comp, hg d]
    change ((E.map a).f n).hom ((p.f n).hom y) = ((E.map a).f n).hom ((q.f n).hom y)
    rw [ha]
    exact congrArg (((E.map (g d)).f n).hom) (hb d)
  · exact (hzero n hn).eq_of_src _ _

end Equality

section Bases

variable {R : Type u} [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {E : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} {t : Cocone E}
variable {A : CochainComplex (ModuleCat.{u} R) ℤ}

/-- For a colimit cocone t of integer-indexed R-module cochain complexes
over a small filtered category J in the universe of the modules, with R
commutative, every element x∈t.ptⁿ is the image of an element y∈Eⱼⁿ
for some stage j. The representative lies in the same cochain degree n. -/
theorem exists_stage_preimage_of_filtered_colimit_element (ht : IsColimit t) {n : ℤ}
    (x : t.pt.X n) :
    ∃ (j : J) (y : (E.obj j).X n), ((t.ι.app j).f n).hom y = x := by
  let F := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n ⋙ forget (ModuleCat.{u} R)
  let c : Cocone (E ⋙ F) := F.mapCocone t
  let hc : IsColimit c := isColimitOfPreserves F ht
  exact Types.jointly_surjective_of_isColimit hc x

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring and t a colimit cocone of module cochain
complexes over a small filtered category J in the universe of the modules.
Suppose A vanishes outside a finite set S of degrees and each Aⁿ for n∈S
has a specified R-basis with a finite index set. For every cochain map
f:A → t.pt, there is one stage j and maps aₙ:Aⁿ → Eⱼⁿ in every degree
such that tⱼⁿ ∘ aₙ=fₙ. -/
theorem exists_stage_degree_factor_of_filtered_colimit_finite_bases (ht : IsColimit t)
    (f : A ⟶ t.pt) (S : Finset ℤ) (I : S → Type u) [∀ n, Finite (I n)]
    (b : ∀ n : S, Module.Basis (I n) R (A.X n)) (hzero : ∀ n ∉ S, IsZero (A.X n)) :
    ∃ (j : J) (a : ∀ n, A.X n ⟶ (E.obj j).X n), ∀ n,
      a n ≫ (t.ι.app j).f n = f.f n := by
  classical
  let W := Σ n : S, I n
  let : Finite W := inferInstanceAs (Finite (Σ n : S, I n))
  let : Fintype W := Fintype.ofFinite W
  have hpre (w : W) : ∃ (j : J) (x : (E.obj j).X w.1),
      ((t.ι.app j).f w.1).hom x = (f.f w.1).hom (b w.1 w.2) :=
    exists_stage_preimage_of_filtered_colimit_element ht _
  choose j x hx using hpre
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let c (w : W) : j w ⟶ k := (hk (Finset.mem_image_of_mem j (Finset.mem_univ w))).some
  let z (w : W) : (E.obj k).X w.1 := ((E.map (c w)).f w.1).hom (x w)
  have hz (w : W) : ((t.ι.app k).f w.1).hom (z w) = (f.f w.1).hom (b w.1 w.2) :=
    (congrArg (fun d => (d.f w.1).hom (x w)) (t.w (c w))).trans (hx w)
  let a (n : ℤ) : A.X n ⟶ (E.obj k).X n :=
    if hn : n ∈ S then ModuleCat.ofHom ((b ⟨n, hn⟩).constr R fun e => z ⟨⟨n, hn⟩, e⟩)
    else 0
  have ha (n : S) (e : I n) : (a n).hom (b n e) = z ⟨n, e⟩ := by
    rcases n with ⟨n, hn⟩
    dsimp only [a]
    rw [dite_eq_left hn, ModuleCat.hom_ofHom, Module.Basis.constr_basis]
  refine ⟨k, a, fun n => ?_⟩
  by_cases hn : n ∈ S
  · let n' : S := ⟨n, hn⟩
    apply ModuleCat.hom_ext
    apply (b n').ext
    intro e
    change ((t.ι.app k).f n).hom ((a n).hom (b n' e)) = (f.f n).hom (b n' e)
    rw [ha n' e]
    exact hz ⟨n', e⟩
  · exact (hzero n hn).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring and t a colimit cocone of module cochain
complexes over a small filtered category J in the universe of the modules.
If A has finite support S and specified finite R-bases for its terms in S,
then every cochain map f:A → t.pt factors as
A → Eⱼ → t.pt for some j, with the first map a cochain map. -/
theorem exists_stage_cochain_factor_of_filtered_colimit_finite_bases (ht : IsColimit t)
    (f : A ⟶ t.pt) (S : Finset ℤ) (I : S → Type u) [∀ n, Finite (I n)]
    (b : ∀ n : S, Module.Basis (I n) R (A.X n)) (hzero : ∀ n ∉ S, IsZero (A.X n)) :
    ∃ (j : J) (g : A ⟶ E.obj j), g ≫ t.ι.app j = f := by
  classical
  obtain ⟨i, a, ha⟩ := exists_stage_degree_factor_of_filtered_colimit_finite_bases ht f S I b hzero
  let p (n : ℤ) : A.X n ⟶ (E.obj i).X (n + 1) := a n ≫ (E.obj i).d n (n + 1)
  let q (n : ℤ) : A.X n ⟶ (E.obj i).X (n + 1) := A.d n (n + 1) ≫ a (n + 1)
  have hpq (n : ℤ) : p n ≫ (t.ι.app i).f (n + 1) = q n ≫ (t.ι.app i).f (n + 1) := by
    calc
      p n ≫ (t.ι.app i).f (n + 1) = (a n ≫ (t.ι.app i).f n) ≫ t.pt.d n (n + 1) := by
        dsimp only [p]
        rw [Category.assoc, ← (t.ι.app i).comm n (n + 1), ← Category.assoc]
        rfl
      _ = f.f n ≫ t.pt.d n (n + 1) := by rw [ha n]
      _ = A.d n (n + 1) ≫ f.f (n + 1) := f.comm n (n + 1)
      _ = q n ≫ (t.ι.app i).f (n + 1) := by
        dsimp only [q]
        rw [Category.assoc, ha (n + 1)]
  let W := Σ n : S, I n
  let : Finite W := inferInstanceAs (Finite (Σ n : S, I n))
  have hsolve (w : W) : ∃ (j : J) (v : i ⟶ j),
      ((E.map v).f ((w.1 : ℤ) + 1)).hom ((p w.1).hom (b w.1 w.2)) =
        ((E.map v).f ((w.1 : ℤ) + 1)).hom ((q w.1).hom (b w.1 w.2)) :=
    exists_stage_eq_of_filtered_colimit_element ht _ _
      (congrArg (fun g => g.hom (b w.1 w.2)) (hpq w.1))
  choose j v hv using hsolve
  obtain ⟨k, d, g, hd⟩ := IsFiltered.wideSpan v
  let m := E.map d
  have hm (n : ℤ) : p n ≫ m.f (n + 1) = q n ≫ m.f (n + 1) := by
    by_cases hn : n ∈ S
    · let n' : S := ⟨n, hn⟩
      apply ModuleCat.hom_ext
      apply (b n').ext
      intro e
      let w : W := ⟨n', e⟩
      have he : m = E.map (v w) ≫ E.map (g w) := by
        rw [← E.map_comp, hd w]
      change (m.f (n + 1)).hom ((p n).hom (b n' e)) =
        (m.f (n + 1)).hom ((q n).hom (b n' e))
      rw [he]
      exact congrArg (((E.map (g w)).f (n + 1)).hom) (hv w)
    · exact (hzero n hn).eq_of_src _ _
  let a' : A ⟶ E.obj k := CochainComplex.ofHom (fun n => a n ≫ m.f n) (fun n => by
    calc
      (a n ≫ m.f n) ≫ (E.obj k).d n (n + 1) = p n ≫ m.f (n + 1) := by
        dsimp only [p]
        rw [Category.assoc, m.comm n (n + 1), ← Category.assoc]
      _ = q n ≫ m.f (n + 1) := hm n
      _ = A.d n (n + 1) ≫ (a (n + 1) ≫ m.f (n + 1)) := Category.assoc _ _ _)
  refine ⟨k, a', ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  change (a n ≫ m.f n) ≫ (t.ι.app k).f n = f.f n
  have h := congrArg (fun x => x.f n) (t.w d)
  rw [Category.assoc]
  exact (congrArg (a n ≫ ·) h).trans (ha n)

end Bases

section Field

variable {R : Type u} [Field R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable {E : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} {t : Cocone E}
variable {A : CochainComplex (ModuleCat.{u} R) ℤ}

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a field and t a colimit cocone of integer-indexed R-vector-space
cochain complexes over a small filtered category J in the universe of the
modules. If A is zero outside a finite set S and Aⁿ is finite-dimensional
for each n∈S, then every cochain map f:A → t.pt factors through a single
stage Eⱼ as a cochain map. -/
theorem exists_stage_cochain_factor_of_filtered_colimit_finite_support (ht : IsColimit t)
    (f : A ⟶ t.pt) (S : Finset ℤ) (hfinite : ∀ n ∈ S, Module.Finite R (A.X n))
    (hzero : ∀ n ∉ S, IsZero (A.X n)) :
    ∃ (j : J) (g : A ⟶ E.obj j), g ≫ t.ι.app j = f := by
  let I (n : S) := Module.Free.ChooseBasisIndex R (A.X n)
  let b (n : S) : Module.Basis (I n) R (A.X n) := Module.Free.chooseBasis R (A.X n)
  let : ∀ n : S, Finite (I n) := fun n => by
    let := hfinite n n.property
    exact Finite.of_fintype (Module.Free.ChooseBasisIndex R (A.X n))
  exact exists_stage_cochain_factor_of_filtered_colimit_finite_bases ht f S I b hzero

end Field

end CochainComplex
