/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Basic

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.EqToHom

/-!
# Compatible original factor prefixes and exact gluing

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C}

/-- The actual factorization of the original caller map through a full source degree truncation. -/
structure PrefixFactor (f : X ⟶ Y) (d : D) where
  /-- The intermediate diagram in the factorization restricted to degrees at most `d`. -/
  Z : r.Through d ⥤ C
  /-- The left factor from the restriction of `X` into the intermediate diagram. -/
  i : (r.throughObjects d).ι ⋙ X ⟶ Z
  /-- The right factor from the intermediate diagram into the restriction of `Y`. -/
  p : Z ⟶ (r.throughObjects d).ι ⋙ Y
  fac : i ≫ p = Functor.whiskerLeft (r.throughObjects d).ι f

namespace PrefixFactor

variable {r} {f : X ⟶ Y} {d e k : D} (a : PrefixFactor r f d)

/-- The complete original coefficient factor record at its unchanged original source object. -/
def component (j : J) (hj : r.degree j ≤ d) :
  MapFactorizationData (⊤ : MorphismProperty C) ⊤ (f.app j) where
  Z := a.Z.obj ⟨j, hj⟩
  i := a.i.app ⟨j, hj⟩
  p := a.p.app ⟨j, hj⟩
  fac := congr_app a.fac ⟨j, hj⟩
  hi := trivial
  hp := trivial

/-- The actual intermediate original-source map at a pair of retained original objects. -/
def map (i j : J) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) (g : i ⟶ j) :
    (a.component i hi).Z ⟶ (a.component j hj).Z :=
  a.Z.map (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Through d) ⟶ ⟨j, hj⟩)

/-- A higher-degree prefix retains each complete lower factor record and every lower
intermediate source map. -/
structure Extends (b : PrefixFactor r f e) (he : e ≤ d) : Prop where
  components (j : J) (hj : r.degree j ≤ e) : a.component j (hj.trans he) = b.component j hj
  maps (i j : J) (hi : r.degree i ≤ e) (hj : r.degree j ≤ e) (g : i ⟶ j) :
    HEq (a.map i j (hi.trans he) (hj.trans he) g) (b.map i j hi hj g)

/-- Every actual prefix retains itself with all original maps and complete factor records. -/
theorem extends_refl : a.Extends a le_rfl where
  components _ _ := rfl
  maps _ _ _ _ _ := HEq.rfl

variable {a} in
/-- Exact original prefix compatibility is transitive on complete coefficient records and
intermediate maps. -/
theorem Extends.trans {b : PrefixFactor r f e} {c : PrefixFactor r f k}
    {he : e ≤ d} {hk : k ≤ e} (hab : a.Extends b he) (hbc : b.Extends c hk) :
    a.Extends c (hk.trans he) where
  components j hj := (hab.components j (hj.trans hk)).trans (hbc.components j hj)
  maps i j hi hj g := (hab.maps i j (hi.trans hk) (hj.trans hk) g).trans (hbc.maps i j hi hj g)

/-- The complete original left coefficient factor equation is retained at every prefix object. -/
theorem component_fac (j : J) (hj : r.degree j ≤ d) :
    (a.component j hj).i ≫ (a.component j hj).p = f.app j := (a.component j hj).fac

/-- Every original prefix intermediate identity is the actual coefficient identity. -/
theorem map_id (j : J) (hj : r.degree j ≤ d) : a.map j j hj hj (𝟙 j) = 𝟙 (a.component j hj).Z :=
  a.Z.map_id ⟨j, hj⟩

/-- Every original prefix intermediate composite is retained on the actual coefficient objects. -/
theorem map_comp (i j k : J) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) (hk : r.degree k ≤ d)
    (g : i ⟶ j) (h : j ⟶ k) :
    a.map i k hi hk (g ≫ h) = a.map i j hi hj g ≫ a.map j k hj hk h :=
  a.Z.map_comp (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Through d) ⟶ ⟨j, hj⟩)
    (ObjectProperty.homMk h : (⟨j, hj⟩ : r.Through d) ⟶ ⟨k, hk⟩)

/-- Every original prefix source-arrow square commutes with its unchanged original left factor
maps. -/
theorem i_naturality (i j : J) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) (g : i ⟶ j) :
    X.map g ≫ (a.component j hj).i = (a.component i hi).i ≫ a.map i j hi hj g :=
  a.i.naturality (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Through d) ⟶ ⟨j, hj⟩)

/-- Every original prefix target-arrow square commutes with its unchanged original right factor
maps. -/
theorem p_naturality (i j : J) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) (g : i ⟶ j) :
    a.map i j hi hj g ≫ (a.component j hj).p = (a.component i hi).p ≫ Y.map g :=
  a.p.naturality (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Through d) ⟶ ⟨j, hj⟩)

end PrefixFactor

end CategoryTheory.ReedyStructure

end ReedyPart1

section ReedyPart2

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure.PrefixGluing

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y)

/-- Supplied actual prefixes, with literal complete coefficient and original-map compatibility. -/
structure Family (allowed : D → Prop) where
  /-- The supplied factorization prefix at each allowed degree. -/
  part (d : D) (hd : allowed d) : PrefixFactor r f d
  compatible {d e : D} (hd : allowed d) (he : allowed e) (hle : e ≤ d) :
    (part d hd).Extends (part e he) hle

variable {r f}

omit [WellFoundedLT D] in
/-- In a linear order the maximum of two allowed degrees is one of those allowed degrees. -/
theorem max_allowed {allowed : D → Prop} {d e : D} (hd : allowed d) (he : allowed e) :
    allowed (max d e) := by
  by_cases h : d ≤ e
  · rw [max_eq_right h]
    exact he
  · rw [max_eq_left (le_of_not_ge h)]
    exact hd

namespace Family

variable {allowed : D → Prop} (a : Family r f allowed)

/-- Select the unchanged original full coefficient record at its own supplied degree. -/
def component (j : J) (hj : allowed (r.degree j)) :
    MapFactorizationData (⊤ : MorphismProperty C) ⊤ (f.app j) :=
  (a.part (r.degree j) hj).component j le_rfl

/-- The selected complete coefficient record is literally every adequate supplied prefix record. -/
theorem component_eq (j : J) (hj : allowed (r.degree j)) (d : D) (hd : allowed d)
    (hjd : r.degree j ≤ d) : a.component j hj = (a.part d hd).component j hjd :=
  ((a.compatible hd hj hjd).components j le_rfl).symm

/-- The original selected intermediate object equals every adequate supplied prefix object. -/
theorem component_Z_eq (j : J) (hj : allowed (r.degree j)) (d : D) (hd : allowed d)
    (hjd : r.degree j ≤ d) : (a.component j hj).Z = ((a.part d hd).component j hjd).Z :=
  congrArg MapFactorizationData.Z (a.component_eq j hj d hd hjd)

/-- Complete coefficient equality retains the original left factor map. -/
theorem component_i_heq (j : J) (hj : allowed (r.degree j)) (d : D) (hd : allowed d)
    (hjd : r.degree j ≤ d) : HEq (a.component j hj).i ((a.part d hd).component j hjd).i :=
  Eq.mp (congrArg (fun c => HEq (a.component j hj).i c.i) (a.component_eq j hj d hd hjd)) HEq.rfl

/-- Complete coefficient equality retains the original right factor map. -/
theorem component_p_heq (j : J) (hj : allowed (r.degree j)) (d : D) (hd : allowed d)
    (hjd : r.degree j ≤ d) : HEq (a.component j hj).p ((a.part d hd).component j hjd).p :=
  Eq.mp (congrArg (fun c => HEq (a.component j hj).p c.p) (a.component_eq j hj d hd hjd)) HEq.rfl

/-- The original arrow is the supplied common-prefix map with its original endpoint transports. -/
def map (i j : J) (hi : allowed (r.degree i)) (hj : allowed (r.degree j)) (g : i ⟶ j) :
    (a.component i hi).Z ⟶ (a.component j hj).Z :=
  eqToHom (a.component_Z_eq i hi (max (r.degree i) (r.degree j))
    (max_allowed hi hj) (le_max_left _ _)) ≫
    (a.part (max (r.degree i) (r.degree j)) (max_allowed hi hj)).map i j
      (le_max_left _ _) (le_max_right _ _) g ≫
    eqToHom (a.component_Z_eq j hj (max (r.degree i) (r.degree j))
      (max_allowed hi hj) (le_max_right _ _)).symm

/-- Every original selected intermediate map is the same map of any adequate supplied prefix. -/
theorem map_heq (i j : J) (hi : allowed (r.degree i)) (hj : allowed (r.degree j)) (g : i ⟶ j)
    (d : D) (hd : allowed d) (hid : r.degree i ≤ d) (hjd : r.degree j ≤ d) :
    HEq (a.map i j hi hj g) ((a.part d hd).map i j hid hjd g) := by
  have h : HEq (a.map i j hi hj g)
      ((a.part (max (r.degree i) (r.degree j)) (max_allowed hi hj)).map i j
        (le_max_left _ _) (le_max_right _ _) g) :=
    (conj_eqToHom_iff_heq _ _
      (a.component_Z_eq i hi (max (r.degree i) (r.degree j)) (max_allowed hi hj) (le_max_left _ _))
      (a.component_Z_eq j hj (max (r.degree i) (r.degree j))
        (max_allowed hi hj) (le_max_right _ _))).mp rfl
  exact h.trans ((a.compatible hd (max_allowed hi hj) (max_le hid hjd)).maps i j
    (le_max_left _ _) (le_max_right _ _) g).symm

/-- The assembled original intermediate identity is the original coefficient identity. -/
theorem map_id (j : J) (hj : allowed (r.degree j))
  : a.map j j hj hj (𝟙 j) = 𝟙 (a.component j hj).Z := by
  have h := a.map_heq j j hj hj (𝟙 j) (r.degree j) hj le_rfl le_rfl
  exact (eq_of_heq h).trans ((a.part (r.degree j) hj).map_id j le_rfl)

/-- The assembled original intermediate maps retain every original composition. -/
theorem map_comp (i j k : J) (hi : allowed (r.degree i)) (hj : allowed (r.degree j))
    (hk : allowed (r.degree k)) (g : i ⟶ j) (h : j ⟶ k) :
    a.map i k hi hk (g ≫ h) = a.map i j hi hj g ≫ a.map j k hj hk h := by
  let d := max (r.degree i) (max (r.degree j) (r.degree k))
  have hd : allowed d := max_allowed hi (max_allowed hj hk)
  have hid : r.degree i ≤ d := le_max_left _ _
  have hjd : r.degree j ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have hkd : r.degree k ≤ d := (le_max_right _ _).trans (le_max_right _ _)
  have hc := heq_comp (a.component_Z_eq i hi d hd hid) (a.component_Z_eq j hj d hd hjd)
    (a.component_Z_eq k hk d hd hkd)
    (a.map_heq i j hi hj g d hd hid hjd) (a.map_heq j k hj hk h d hd hjd hkd)
  exact eq_of_heq ((a.map_heq i k hi hk (g ≫ h) d hd hid hkd).trans
    (heq_of_eq ((a.part d hd).map_comp i j k hid hjd hkd g h)) |>.trans hc.symm)

/-- Every original source arrow commutes with the assembled original left factor maps. -/
theorem i_naturality (i j : J) (hi : allowed (r.degree i)) (hj : allowed (r.degree j)) (g : i ⟶ j) :
    X.map g ≫ (a.component j hj).i = (a.component i hi).i ≫ a.map i j hi hj g := by
  let d := max (r.degree i) (r.degree j)
  have hd : allowed d := max_allowed hi hj
  have hid : r.degree i ≤ d := le_max_left _ _
  have hjd : r.degree j ≤ d := le_max_right _ _
  have hl := heq_comp (rfl : X.obj i = X.obj i) (rfl : X.obj j = X.obj j)
    (a.component_Z_eq j hj d hd hjd) (HEq.rfl (a := X.map g)) (a.component_i_heq j hj d hd hjd)
  have hr := heq_comp (rfl : X.obj i = X.obj i) (a.component_Z_eq i hi d hd hid)
    (a.component_Z_eq j hj d hd hjd) (a.component_i_heq i hi d hd hid)
      (a.map_heq i j hi hj g d hd hid hjd)
  exact eq_of_heq (hl.trans (heq_of_eq ((a.part d hd).i_naturality i j hid hjd g)) |>.trans hr.symm)

/-- Every original target arrow commutes with the assembled original right factor maps. -/
theorem p_naturality (i j : J) (hi : allowed (r.degree i)) (hj : allowed (r.degree j)) (g : i ⟶ j) :
    a.map i j hi hj g ≫ (a.component j hj).p = (a.component i hi).p ≫ Y.map g := by
  let d := max (r.degree i) (r.degree j)
  have hd : allowed d := max_allowed hi hj
  have hid : r.degree i ≤ d := le_max_left _ _
  have hjd : r.degree j ≤ d := le_max_right _ _
  have hl := heq_comp (a.component_Z_eq i hi d hd hid) (a.component_Z_eq j hj d hd hjd)
    (rfl : Y.obj j = Y.obj j) (a.map_heq i j hi hj g d hd hid hjd) (a.component_p_heq j hj d hd hjd)
  have hr := heq_comp (a.component_Z_eq i hi d hd hid) (rfl : Y.obj i = Y.obj i)
    (rfl : Y.obj j = Y.obj j) (a.component_p_heq i hi d hd hid) (HEq.rfl (a := Y.map g))
  exact eq_of_heq (hl.trans (heq_of_eq ((a.part d hd).p_naturality i j hid hjd g)) |>.trans hr.symm)

end Family

end CategoryTheory.ReedyStructure.PrefixGluing

end ReedyPart2

section ReedyPart3

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure.PrefixGluing

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y)

/-- Read the complete original coefficient record from an actual natural factor record. -/
def coefficient {S : Type uS} [Category.{vS} S] {A B : S ⥤ C} {t : A ⟶ B}
    (a : MapFactorizationData (⊤ : MorphismProperty (S ⥤ C)) ⊤ t) (j : S) :
    MapFactorizationData (⊤ : MorphismProperty C) ⊤ (t.app j) where
  Z := a.Z.obj j
  i := a.i.app j
  p := a.p.app j
  fac := congr_app a.fac j
  hi := trivial
  hp := trivial

/-- The full original objects at the allowed source degrees. -/
abbrev familyObjects (allowed : D → Prop) : ObjectProperty J := fun j => allowed (r.degree j)

namespace Family

variable {r f} {allowed : D → Prop} (a : Family r f allowed)

/-- The supplied original coefficients and maps form a diagram on every allowed original object. -/
def diagram : (familyObjects r allowed).FullSubcategory ⥤ C where
  obj j := (a.component j.obj j.property).Z
  map {i j} g := a.map i.obj j.obj i.property j.property g.hom
  map_id j := a.map_id j.obj j.property
  map_comp {i j k} g h := a.map_comp i.obj j.obj k.obj i.property j.property k.property g.hom h.hom

/-- The unchanged original left coefficient maps form the full natural left factor. -/
def leftTransformation : (familyObjects r allowed).ι ⋙ X ⟶ a.diagram where
  app j := (a.component j.obj j.property).i
  naturality i j g := a.i_naturality i.obj j.obj i.property j.property g.hom

/-- The unchanged original right coefficient maps form the full natural right factor. -/
def rightTransformation : a.diagram ⟶ (familyObjects r allowed).ι ⋙ Y where
  app j := (a.component j.obj j.property).p
  naturality i j g := a.p_naturality i.obj j.obj i.property j.property g.hom

/-- The complete factor on the full allowed original source, assembled from the actual supplied
prefixes. -/
def factor : MapFactorizationData
    (⊤ : MorphismProperty ((familyObjects r allowed).FullSubcategory ⥤ C)) ⊤
    (Functor.whiskerLeft (familyObjects r allowed).ι f) where
  Z := a.diagram
  i := a.leftTransformation
  p := a.rightTransformation
  fac := by
    ext j
    exact (a.component j.obj j.property).fac
  hi := trivial
  hp := trivial

/-- The assembled full-source coefficient is the same complete selected original record. -/
theorem factor_coefficient (j : J) (hj : allowed (r.degree j)) :
    coefficient a.factor (⟨j, hj⟩ : (familyObjects r allowed).FullSubcategory) =
      a.component j hj := rfl

end Family

namespace CompleteFamily

variable {r f} (a : Family r f (fun _ => True))

/-- The complete original intermediate diagram, using each original J object and every original
J arrow. -/
def diagram : J ⥤ C where
  obj j := (a.component j trivial).Z
  map {i j} g := a.map i j trivial trivial g
  map_id j := a.map_id j trivial
  map_comp {i j k} g h := a.map_comp i j k trivial trivial trivial g h

/-- Compatible supplied prefixes assemble the complete unchanged original natural factorization. -/
def factor : MapFactorizationData (⊤ : MorphismProperty (J ⥤ C)) ⊤ f where
  Z := diagram a
  i :=
    { app j := (a.component j trivial).i
      naturality i j g := a.i_naturality i j trivial trivial g }
  p :=
    { app j := (a.component j trivial).p
      naturality i j g := a.p_naturality i j trivial trivial g }
  fac := by
    ext j
    exact (a.component j trivial).fac
  hi := trivial
  hp := trivial

/-- The complete original factor retains the selected complete coefficient at every original
object. -/
theorem factor_coefficient (j : J) : coefficient (factor a) j = a.component j trivial := rfl

end CompleteFamily

/-- Package exactly the supplied compatible strict lower-degree original prefixes. -/
def lowerFamily (d : D) (a : ∀ e : D, e < d → PrefixFactor r f e)
    (h : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
      (a e' he').Extends (a e he) hle) : Family r f (fun e => e < d) where
  part := a
  compatible hd he hle := h _ _ he hd hle

/-- The supplied compatible smaller prefixes construct an actual natural factor on the entire
original lower source. -/
def lowerFactor (d : D) (a : ∀ e : D, e < d → PrefixFactor r f e)
    (h : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
      (a e' he').Extends (a e he) hle) :
    MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
      (Functor.whiskerLeft (r.belowObjects d).ι f) :=
  (lowerFamily r f d a h).factor

/-- Every lower assembled coefficient is literally the original record of every adequate caller
prefix. -/
theorem lowerFactor_coefficient (d : D) (a : ∀ e : D, e < d → PrefixFactor r f e)
    (h : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
      (a e' he').Extends (a e he) hle)
    (j : J) (hj : r.degree j < d) (e : D) (he : e < d) (hje : r.degree j ≤ e) :
    coefficient (lowerFactor r f d a h) (⟨j, hj⟩ : r.Below d) = (a e he).component j hje := by
  change coefficient (lowerFamily r f d a h).factor ⟨j, hj⟩ = (a e he).component j hje
  rw [Family.factor_coefficient]
  exact (lowerFamily r f d a h).component_eq j hj e he hje

/-- Every original intermediate lower map is the actual map in every adequate caller prefix. -/
theorem lowerFactor_map_heq (d : D) (a : ∀ e : D, e < d → PrefixFactor r f e)
    (h : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
      (a e' he').Extends (a e he) hle)
    (i j : J) (hi : r.degree i < d) (hj : r.degree j < d) (g : i ⟶ j)
    (e : D) (he : e < d) (hie : r.degree i ≤ e) (hje : r.degree j ≤ e) :
    HEq ((lowerFactor r f d a h).Z.map
      (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩))
      ((a e he).map i j hie hje g) :=
  (lowerFamily r f d a h).map_heq i j hi hj g e he hie hje

/-- The lower assembled natural factor retains the unchanged original restricted source map. -/
theorem lowerFactor_fac (d : D) (a : ∀ e : D, e < d → PrefixFactor r f e)
    (h : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
      (a e' he').Extends (a e he) hle) :
    (lowerFactor r f d a h).i ≫ (lowerFactor r f d a h).p =
      Functor.whiskerLeft (r.belowObjects d).ι f := (lowerFactor r f d a h).fac

/-- Package exactly the supplied compatible original prefixes through every source degree. -/
def completeFamily (a : ∀ d : D, PrefixFactor r f d)
    (h : ∀ (d e : D) (hle : e ≤ d), (a d).Extends (a e) hle) : Family r f (fun _ => True) where
  part d _ := a d
  compatible _hd _he hle := h _ _ hle

/-- Compatible supplied degree prefixes construct the full factor on every original J object and
arrow. -/
def fullFactor (a : ∀ d : D, PrefixFactor r f d)
    (h : ∀ (d e : D) (hle : e ≤ d), (a d).Extends (a e) hle) :
    MapFactorizationData (⊤ : MorphismProperty (J ⥤ C)) ⊤ f :=
  CompleteFamily.factor (completeFamily r f a h)

/-- Every full assembled coefficient is literally the original record of every adequate caller
prefix. -/
theorem fullFactor_coefficient (a : ∀ d : D, PrefixFactor r f d)
    (h : ∀ (d e : D) (hle : e ≤ d), (a d).Extends (a e) hle)
    (j : J) (d : D) (hj : r.degree j ≤ d) :
    coefficient (fullFactor r f a h) j = (a d).component j hj := by
  change coefficient (CompleteFamily.factor (completeFamily r f a h)) j = (a d).component j hj
  rw [CompleteFamily.factor_coefficient]
  exact (completeFamily r f a h).component_eq j trivial d trivial hj

/-- Every full intermediate original map is the actual map in every adequate caller prefix. -/
theorem fullFactor_map_heq (a : ∀ d : D, PrefixFactor r f d)
    (h : ∀ (d e : D) (hle : e ≤ d), (a d).Extends (a e) hle)
    (i j : J) (g : i ⟶ j) (d : D) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) :
    HEq ((fullFactor r f a h).Z.map g) ((a d).map i j hi hj g) :=
  (completeFamily r f a h).map_heq i j trivial trivial g d trivial hi hj

/-- The complete assembled natural factor retains the unchanged full original source map. -/
theorem fullFactor_fac (a : ∀ d : D, PrefixFactor r f d)
    (h : ∀ (d e : D) (hle : e ≤ d), (a d).Extends (a e) hle) :
    (fullFactor r f a h).i ≫ (fullFactor r f a h).p = f := (fullFactor r f a h).fac

end CategoryTheory.ReedyStructure.PrefixGluing

end ReedyPart3

section ReedyPart4

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure.PrefixGluing

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y)
  (A : ∀ d : D, PrefixFactor r f d)
  (hA : ∀ (d e : D) (hle : e ≤ d), (A d).Extends (A e) hle) (d : D)

/-- The glued middle object at each retained original object is the exact prefix object. -/
theorem fullMiddle_obj_eq (q : r.Through d) :
    (fullFactor r f A hA).Z.obj q.obj = (A d).Z.obj q :=
  congrArg MapFactorizationData.Z (fullFactor_coefficient r f A hA q.obj d q.property)

/-- Every original restricted intermediate map commutes with the exact coefficient comparison. -/
theorem fullMiddle_naturality {q q' : r.Through d} (g : q ⟶ q') :
    (fullFactor r f A hA).Z.map g.hom ≫ eqToHom (fullMiddle_obj_eq r f A hA d q') =
      eqToHom (fullMiddle_obj_eq r f A hA d q) ≫ (A d).Z.map g := by
  have hm := (conj_eqToHom_iff_heq _ _
    (fullMiddle_obj_eq r f A hA d q) (fullMiddle_obj_eq r f A hA d q')).mpr
    (fullFactor_map_heq r f A hA q.obj q'.obj g.hom d q.property q'.property)
  have hg : (ObjectProperty.homMk g.hom : q ⟶ q') = g := by
    apply ObjectProperty.hom_ext
    rfl
  dsimp only [PrefixFactor.map] at hm
  rw [hg] at hm
  apply (comp_eqToHom_iff (fullMiddle_obj_eq r f A hA d q') _ _).mpr
  simpa only [Category.assoc] using hm

/-- The complete original glued middle diagram restricts naturally to each supplied actual
prefix. -/
def fullMiddleIso : (r.throughObjects d).ι ⋙ (fullFactor r f A hA).Z ≅ (A d).Z :=
  NatIso.ofComponents (fun q => eqToIso (fullMiddle_obj_eq r f A hA d q))
    (fun g => fullMiddle_naturality r f A hA d g)

/-- Each original comparison component is the exact original coefficient object transport. -/
theorem fullMiddleIso_hom_app (q : r.Through d) :
    (fullMiddleIso r f A hA d).hom.app q = eqToHom (fullMiddle_obj_eq r f A hA d q) := rfl

/-- Each inverse comparison component retains the inverse original coefficient object transport. -/
theorem fullMiddleIso_inv_app (q : r.Through d) :
    (fullMiddleIso r f A hA d).inv.app q = eqToHom (fullMiddle_obj_eq r f A hA d q).symm := rfl

/-- The unchanged original left factor maps commute with the complete prefix comparison. -/
theorem fullLeft_comparison :
    Functor.whiskerLeft (r.throughObjects d).ι (fullFactor r f A hA).i ≫
      (fullMiddleIso r f A hA d).hom = (A d).i := by
  ext q
  have hi : HEq ((fullFactor r f A hA).i.app q.obj) ((A d).i.app q) :=
    Eq.mp (congrArg (fun a => HEq ((fullFactor r f A hA).i.app q.obj) a.i)
      (fullFactor_coefficient r f A hA q.obj d q.property)) HEq.rfl
  have hc := (conj_eqToHom_iff_heq _ _ (rfl : X.obj q.obj = X.obj q.obj)
    (fullMiddle_obj_eq r f A hA d q)).mpr hi
  change (fullFactor r f A hA).i.app q.obj ≫ eqToHom (fullMiddle_obj_eq r f A hA d q) = _
  rw [hc]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, eqToHom_trans, Category.comp_id]

/-- The unchanged original right factor maps commute with the complete prefix comparison. -/
theorem fullRight_comparison :
    (fullMiddleIso r f A hA d).hom ≫ (A d).p =
      Functor.whiskerLeft (r.throughObjects d).ι (fullFactor r f A hA).p := by
  ext q
  have hp : HEq ((fullFactor r f A hA).p.app q.obj) ((A d).p.app q) :=
    Eq.mp (congrArg (fun a => HEq ((fullFactor r f A hA).p.app q.obj) a.p)
      (fullFactor_coefficient r f A hA q.obj d q.property)) HEq.rfl
  have hc := (conj_eqToHom_iff_heq _ _ (fullMiddle_obj_eq r f A hA d q)
    (rfl : Y.obj q.obj = Y.obj q.obj)).mpr hp
  change eqToHom (fullMiddle_obj_eq r f A hA d q) ≫ (A d).p.app q =
    (fullFactor r f A hA).p.app q.obj
  simpa only [eqToHom_refl, Category.comp_id] using hc.symm

/-- The full original left factor restricted through a degree is the supplied prefix left arrow. -/
def fullLeftArrowIso :
    Arrow.mk (Functor.whiskerLeft (r.throughObjects d).ι (fullFactor r f A hA).i) ≅
      Arrow.mk (A d).i :=
  Arrow.isoMk' _ _ (Iso.refl _) (fullMiddleIso r f A hA d) (by
    rw [Iso.refl_hom, Category.id_comp]
    exact (fullLeft_comparison r f A hA d).symm)

/-- The full original right factor restricted through a degree is the supplied prefix right
arrow. -/
def fullRightArrowIso :
    Arrow.mk (Functor.whiskerLeft (r.throughObjects d).ι (fullFactor r f A hA).p) ≅
      Arrow.mk (A d).p :=
  Arrow.isoMk' _ _ (fullMiddleIso r f A hA d) (Iso.refl _) (by
    rw [Iso.refl_hom, Category.comp_id]
    exact fullRight_comparison r f A hA d)

end CategoryTheory.ReedyStructure.PrefixGluing

end ReedyPart4
