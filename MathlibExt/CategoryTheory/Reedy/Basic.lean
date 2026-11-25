/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.Order.WithBot
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.Order.RelClasses

/-!
# Ordinary Reedy structures and their original source factorizations

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

namespace CategoryTheory

open MorphismProperty

variable {J : Type uJ} [Category.{vJ} J]

/-- The original inverse--direct record is Mathlib's complete map factorization record. -/
abbrev ReedyFactorization (direct inverse : MorphismProperty J) {i j : J} (f : i ⟶ j) :=
  inverse.MapFactorizationData direct f

namespace ReedyFactorization

variable {direct inverse : MorphismProperty J} {i j : J} {f : i ⟶ j}

/-- The original middle-object accessor on the canonical record. -/
abbrev middle (a : ReedyFactorization direct inverse f) : J := a.Z

/-- The original inverse-map accessor on the canonical record. -/
abbrev inverseMap (a : ReedyFactorization direct inverse f) : i ⟶ a.middle := a.i

/-- The original direct-map accessor on the canonical record. -/
abbrev directMap (a : ReedyFactorization direct inverse f) : a.middle ⟶ j := a.p

/-- The original inverse membership is the canonical first-factor membership. -/
theorem inverse_mem (a : ReedyFactorization direct inverse f) : inverse a.inverseMap := a.hi

/-- The original direct membership is the canonical second-factor membership. -/
theorem direct_mem (a : ReedyFactorization direct inverse f) : direct a.directMap := a.hp

/-- The original constructor order, transparently interpreted in Mathlib's factor record. -/
abbrev mk (middle : J) (inverseMap : i ⟶ middle) (directMap : middle ⟶ j)
    (inverse_mem : inverse inverseMap) (direct_mem : direct directMap)
    (fac : inverseMap ≫ directMap = f) : ReedyFactorization direct inverse f :=
  ⟨middle, inverseMap, directMap, fac, inverse_mem, direct_mem⟩

end ReedyFactorization

namespace ReedyStructure

/-- The canonical successor on the enlarged original well order, requiring no extra hypotheses. -/
abbrev canonicalDegreeSuccOrder (D : Type uD) [LinearOrder D] [WellFoundedLT D] :
    SuccOrder (WithBot D) := SuccOrder.ofLinearWellFoundedLT _

attribute [scoped instance] canonicalDegreeSuccOrder

end ReedyStructure

open scoped ReedyStructure

/-- A compatibility interface for the original degree and chosen maps on native Reedy data.
The canonical degree is the exact order embedding into `WithBot D`, in the same universe. -/
structure ReedyStructure (J : Type uJ) [Category.{vJ} J]
    (D : Type uD) [LinearOrder D] [WellFoundedLT D] where
  ofCanonicalData ::
  /-- The unchanged original degree. -/
  degree : J → D
  /-- The unchanged original direct class. -/
  direct : MorphismProperty J
  /-- The unchanged original inverse class. -/
  inverse : MorphismProperty J
  direct_multiplicative : direct.IsMultiplicative
  inverse_multiplicative : inverse.IsMultiplicative
  /-- Native Reedy data, using the canonical bottom and successor adapter. -/
  native : @HomotopicalAlgebra.ReedyStructure J _ inverse direct
    inverse_multiplicative direct_multiplicative (WithBot D) _ _
      (SuccOrder.ofLinearWellFoundedLT _) _
  native_degree (j : J) : native.deg j = (degree j : WithBot D)
  /-- The same originally supplied choice, in Mathlib's factor record. -/
  factor {i j : J} (f : i ⟶ j) : ReedyFactorization direct inverse f

attribute [instance] ReedyStructure.direct_multiplicative ReedyStructure.inverse_multiplicative

namespace ReedyStructure

variable {D : Type uD} [LinearOrder D] [WellFoundedLT D]

/-- The complete original constructor derives canonical Reedy data from the original assumptions. -/
abbrev mk (degree : J → D) (direct inverse : MorphismProperty J)
    (direct_multiplicative : direct.IsMultiplicative)
    (inverse_multiplicative : inverse.IsMultiplicative)
    (direct_le : ∀ {i j : J} (f : i ⟶ j), direct f → degree i ≤ degree j)
    (inverse_le : ∀ {i j : J} (f : i ⟶ j), inverse f → degree j ≤ degree i)
    (direct_equal : ∀ {i j : J} (f : i ⟶ j), direct f → degree i = degree j →
      ∃ h : i = j, f = eqToHom h)
    (inverse_equal : ∀ {i j : J} (f : i ⟶ j), inverse f → degree i = degree j →
      ∃ h : i = j, f = eqToHom h)
    (factor : ∀ {i j : J} (f : i ⟶ j), ReedyFactorization direct inverse f)
    (factor_unique : ∀ {i j : J} (f : i ⟶ j)
      (a b : ReedyFactorization direct inverse f), a = b) : ReedyStructure J D where
  degree := degree
  direct := direct
  inverse := inverse
  direct_multiplicative := direct_multiplicative
  inverse_multiplicative := inverse_multiplicative
  native :=
    { deg j := (degree j : WithBot D)
      lt₁ f hf hf' := WithBot.coe_lt_coe.mpr (by
        refine lt_of_le_of_ne (inverse_le f hf) ?_
        intro he
        obtain ⟨e, h⟩ := inverse_equal f hf he.symm
        subst e
        apply hf'
        rw [h]
        exact .mk _)
      lt₂ f hf hf' := WithBot.coe_lt_coe.mpr (by
        refine lt_of_le_of_ne (direct_le f hf) ?_
        intro he
        obtain ⟨e, h⟩ := direct_equal f hf he
        subst e
        apply hf'
        rw [h]
        exact .mk _)
      nonempty_unique f :=
        ⟨{ default := factor f, uniq := fun a => factor_unique f a (factor f) }⟩ }
  native_degree _ := rfl
  factor := factor

variable (r : ReedyStructure J D)

/-- The native Reedy structure retains exactly the original direct and inverse classes. -/
abbrev toCanonical : @HomotopicalAlgebra.ReedyStructure J _ r.inverse r.direct
    r.inverse_multiplicative r.direct_multiplicative (WithBot D) _ _
      (SuccOrder.ofLinearWellFoundedLT _) _ := r.native

/-- The native degree is the original degree under its exact canonical order embedding. -/
@[simp]
theorem toCanonical_degree (j : J) : r.toCanonical.deg j = (r.degree j : WithBot D) :=
  r.native_degree j

/-- Native strict degree comparison is exactly the original strict degree comparison. -/
theorem toCanonical_degree_lt {i j : J} :
    r.toCanonical.deg i < r.toCanonical.deg j ↔ r.degree i < r.degree j := by
  rw [r.toCanonical_degree, r.toCanonical_degree, WithBot.coe_lt_coe]

/-- Native weak degree comparison is exactly the original weak degree comparison. -/
theorem toCanonical_degree_le {i j : J} :
    r.toCanonical.deg i ≤ r.toCanonical.deg j ↔ r.degree i ≤ r.degree j := by
  rw [r.toCanonical_degree, r.toCanonical_degree, WithBot.coe_le_coe]

/-- Native degree equality is exactly equality of the original degrees. -/
theorem toCanonical_degree_eq {i j : J} :
    r.toCanonical.deg i = r.toCanonical.deg j ↔ r.degree i = r.degree j := by
  rw [r.toCanonical_degree, r.toCanonical_degree, WithBot.coe_eq_coe]

/-- Direct monotonicity is supplied by Mathlib's native Reedy degree API. -/
theorem direct_le {i j : J} (f : i ⟶ j) (hf : r.direct f) : r.degree i ≤ r.degree j :=
  r.toCanonical_degree_le.mp (r.native.le₂ f hf)

/-- Inverse monotonicity is supplied by Mathlib's native Reedy degree API. -/
theorem inverse_le {i j : J} (f : i ⟶ j) (hf : r.inverse f) : r.degree j ≤ r.degree i :=
  r.toCanonical_degree_le.mp (r.native.le₁ f hf)

/-- Native direct identities retain the original object equality and original transport map. -/
theorem direct_equal {i j : J} (f : i ⟶ j) (hf : r.direct f)
    (h : r.degree i = r.degree j) : ∃ e : i = j, f = eqToHom e := by
  have hi := r.native.identities_of_prop₂_of_eq hf (r.toCanonical_degree_eq.mpr h)
  cases hi
  exact ⟨rfl, rfl⟩

/-- Native inverse identities retain the original object equality and original transport map. -/
theorem inverse_equal {i j : J} (f : i ⟶ j) (hf : r.inverse f)
    (h : r.degree i = r.degree j) : ∃ e : i = j, f = eqToHom e := by
  have hi := r.native.identities_of_prop₁_of_eq hf (r.toCanonical_degree_eq.mpr h)
  cases hi
  exact ⟨rfl, rfl⟩

/-- Complete original factor equality is Mathlib's native uniqueness assertion. -/
theorem factor_unique {i j : J} (f : i ⟶ j)
    (a b : ReedyFactorization r.direct r.inverse f) : a = b := by
  let := r.native.subsingleton_mapFactorizationData f
  exact Subsingleton.elim _ _

/-- Native uniqueness determines the entire compatibility interface
from its original source data. -/
@[ext]
theorem ext {J : Type uJ} [Category.{vJ} J]
    {D : Type uD} [LinearOrder D] [WellFoundedLT D]
    (r s : CategoryTheory.ReedyStructure J D)
    (hdegree : r.degree = s.degree) (hdirect : r.direct = s.direct)
    (hinverse : r.inverse = s.inverse) : r = s := by
  rcases r with ⟨rd, rdirect, rinverse, rdm, rim, rn, rdegree, rf⟩
  rcases s with ⟨sd, sdirect, sinverse, sdm, sim, sn, sdegree, sf⟩
  cases hdegree
  cases hdirect
  cases hinverse
  have hn : rn = sn := by
    cases rn with
    | mk rdeg rlt₁ rlt₂ runique =>
      cases sn with
      | mk sdeg slt₁ slt₂ sunique =>
        have h : rdeg = sdeg := funext (fun j => (rdegree j).trans (sdegree j).symm)
        cases h
        rfl
  cases hn
  have hf : @rf = @sf := by
    funext i j f
    let := rn.subsingleton_mapFactorizationData f
    exact Subsingleton.elim _ _
  cases hf
  rfl

/-- Mathlib's selected complete factor is the originally supplied complete record. -/
theorem toCanonical_mapFactorizationData {i j : J} (f : i ⟶ j) :
    r.toCanonical.mapFactorizationData f = r.factor f :=
  r.factor_unique f _ _

/-- A native Reedy structure gives the compatibility interface without changing any source maps. -/
def ofCanonical {direct inverse : MorphismProperty J}
    [direct.IsMultiplicative] [inverse.IsMultiplicative]
    [OrderBot D] [SuccOrder D]
    (s : HomotopicalAlgebra.ReedyStructure inverse direct D) : ReedyStructure J D :=
  mk s.deg direct inverse inferInstance inferInstance s.le₂ s.le₁
    (fun f hf h => by
      have hi := s.identities_of_prop₂_of_eq hf h
      cases hi
      exact ⟨rfl, rfl⟩)
    (fun f hf h => by
      have hi := s.identities_of_prop₁_of_eq hf h
      cases hi
      exact ⟨rfl, rfl⟩)
    s.mapFactorizationData (fun f _ _ => by
      let := s.subsingleton_mapFactorizationData f
      exact Subsingleton.elim _ _)

/-- The actual direct wide subcategory retains every original object. -/
abbrev Direct := WideSubcategory r.direct

/-- The actual inverse wide subcategory retains every original object. -/
abbrev Inverse := WideSubcategory r.inverse

/-- The actual direct inclusion preserves every original arrow. -/
abbrev directInclusion : r.Direct ⥤ J := wideSubcategoryInclusion r.direct

/-- The actual inverse inclusion preserves every original arrow. -/
abbrev inverseInclusion : r.Inverse ⥤ J := wideSubcategoryInclusion r.inverse

/-- The factorization's middle lies below its original source degree. -/
theorem middle_le_source {i j : J} (f : i ⟶ j) :
    r.degree (r.factor f).middle ≤ r.degree i :=
  r.inverse_le _ (r.factor f).inverse_mem

/-- The factorization's middle lies below its original target degree. -/
theorem middle_le_target {i j : J} (f : i ⟶ j) :
    r.degree (r.factor f).middle ≤ r.degree j :=
  r.direct_le _ (r.factor f).direct_mem

/-- A direct arrow whose degree does not strictly rise is the actual identity transport. -/
theorem direct_identity_of_not_lt {i j : J} (f : i ⟶ j) (hf : r.direct f)
    (h : ¬ r.degree i < r.degree j) : ∃ e : i = j, f = eqToHom e :=
  r.direct_equal f hf (le_antisymm (r.direct_le f hf) (le_of_not_gt h))

/-- An inverse arrow whose degree does not strictly fall is the actual identity transport. -/
theorem inverse_identity_of_not_lt {i j : J} (f : i ⟶ j) (hf : r.inverse f)
    (h : ¬ r.degree j < r.degree i) : ∃ e : i = j, f = eqToHom e :=
  r.inverse_equal f hf (le_antisymm (le_of_not_gt h) (r.inverse_le f hf))

/-- Naturality on the two actual wide subcategories implies naturality on every source arrow. -/
theorem naturality_of_direct_inverse {C : Type*} [Category* C] {X Y : J ⥤ C}
    (a : ∀ j, X.obj j ⟶ Y.obj j)
    (hd : ∀ {i j : J} (f : i ⟶ j), r.direct f → X.map f ≫ a j = a i ≫ Y.map f)
    (hi : ∀ {i j : J} (f : i ⟶ j), r.inverse f → X.map f ≫ a j = a i ≫ Y.map f)
    {i j : J} (f : i ⟶ j) : X.map f ≫ a j = a i ≫ Y.map f := by
  rw [← (r.factor f).fac, X.map_comp, Y.map_comp, Category.assoc,
    hd _ (r.factor f).direct_mem, ← Category.assoc, hi _ (r.factor f).inverse_mem,
    Category.assoc]

end ReedyStructure

end CategoryTheory

end ReedyPart1

section ReedyPart2

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  (C : Type uC) [Category.{vC} C]

/-- Actual object values, direct/inverse maps, and their original mixed composition relation. -/
structure NormalFunctorData where
  /-- The object assignment of the functor assembled from the supplied direct and inverse maps. -/
  obj : J → C
  /-- The image of each arrow belonging to the direct subcategory. -/
  directMap {i j : J} (f : i ⟶ j) (hf : r.direct f) : obj i ⟶ obj j
  /-- The image of each arrow belonging to the inverse subcategory. -/
  inverseMap {i j : J} (f : i ⟶ j) (hf : r.inverse f) : obj i ⟶ obj j
  direct_id (i : J) : directMap (𝟙 i) (r.direct.id_mem i) = 𝟙 (obj i)
  inverse_id (i : J) : inverseMap (𝟙 i) (r.inverse.id_mem i) = 𝟙 (obj i)
  direct_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (hf : r.direct f) (hg : r.direct g) :
    directMap (f ≫ g) (r.direct.comp_mem _ _ hf hg) = directMap f hf ≫ directMap g hg
  inverse_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (hf : r.inverse f) (hg : r.inverse g) :
    inverseMap (f ≫ g) (r.inverse.comp_mem _ _ hf hg) = inverseMap f hf ≫ inverseMap g hg
  interchange {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (hf : r.direct f) (hg : r.inverse g) :
    directMap f hf ≫ inverseMap g hg =
      inverseMap (r.factor (f ≫ g)).inverseMap (r.factor (f ≫ g)).inverse_mem ≫
      directMap (r.factor (f ≫ g)).directMap (r.factor (f ≫ g)).direct_mem

namespace NormalFunctorData

variable {r C} (a : NormalFunctorData r C)

/-- Evaluation of a complete original inverse--direct factor record. -/
def evaluate {i j : J} {f : i ⟶ j} (d : ReedyFactorization r.direct r.inverse f)
  : a.obj i ⟶ a.obj j :=
  a.inverseMap d.inverseMap d.inverse_mem ≫ a.directMap d.directMap d.direct_mem

/-- Unique original factor records have the same evaluation without changing any of their maps. -/
theorem evaluate_eq {i j : J} {f : i ⟶ j} (d e : ReedyFactorization r.direct r.inverse f) :
    a.evaluate d = a.evaluate e := congrArg a.evaluate (r.factor_unique f d e)

/-- The original full source map obtained from its canonical inverse--direct record. -/
def map {i j : J} (f : i ⟶ j) : a.obj i ⟶ a.obj j := a.evaluate (r.factor f)

/-- The assembled map of an actual direct arrow is the same supplied direct map. -/
theorem map_direct {i j : J} (f : i ⟶ j) (hf : r.direct f) : a.map f = a.directMap f hf := by
  let d : ReedyFactorization r.direct r.inverse f :=
    ReedyFactorization.mk i (𝟙 i) f (r.inverse.id_mem i) hf (Category.id_comp f)
  rw [map, a.evaluate_eq (r.factor f) d]
  dsimp only [evaluate, d]
  rw [a.inverse_id, Category.id_comp]

/-- The assembled map of an actual inverse arrow is the same supplied inverse map. -/
theorem map_inverse {i j : J} (f : i ⟶ j) (hf : r.inverse f) : a.map f = a.inverseMap f hf := by
  let d : ReedyFactorization r.direct r.inverse f :=
    ReedyFactorization.mk j f (𝟙 j) hf (r.direct.id_mem j) (Category.comp_id f)
  rw [map, a.evaluate_eq (r.factor f) d]
  dsimp only [evaluate, d]
  rw [a.direct_id, Category.comp_id]

/-- The assembled full source map preserves the original identity. -/
theorem map_id (i : J) : a.map (𝟙 i) = 𝟙 (a.obj i) := by
  rw [a.map_direct _ (r.direct.id_mem i), a.direct_id]

/-- The assembled full source map preserves every original composite. -/
theorem map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) : a.map (f ≫ g) = a.map f ≫ a.map g := by
  let d := r.factor f
  let e := r.factor g
  let c := r.factor (d.directMap ≫ e.inverseMap)
  let h : ReedyFactorization r.direct r.inverse (f ≫ g) :=
    { Z := c.middle
      i := d.inverseMap ≫ c.inverseMap
      p := c.directMap ≫ e.directMap
      hi := r.inverse.comp_mem _ _ d.inverse_mem c.inverse_mem
      hp := r.direct.comp_mem _ _ c.direct_mem e.direct_mem
      fac := by
        calc
          _ = d.inverseMap ≫ (c.inverseMap ≫ c.directMap) ≫ e.directMap := by
            simp only [Category.assoc]
          _ = d.inverseMap ≫ (d.directMap ≫ e.inverseMap) ≫ e.directMap := by rw [c.fac]
          _ = (d.inverseMap ≫ d.directMap) ≫ (e.inverseMap ≫ e.directMap) := by
            simp only [Category.assoc]
          _ = f ≫ g := by rw [d.fac, e.fac] }
  rw [map, a.evaluate_eq (r.factor (f ≫ g)) h]
  change a.inverseMap (d.inverseMap ≫ c.inverseMap) _ ≫
    a.directMap (c.directMap ≫ e.directMap) _ = _
  rw [a.inverse_comp d.inverseMap c.inverseMap d.inverse_mem c.inverse_mem,
    a.direct_comp c.directMap e.directMap c.direct_mem e.direct_mem]
  calc
    _ = a.inverseMap d.inverseMap d.inverse_mem ≫
      (a.inverseMap c.inverseMap c.inverse_mem ≫ a.directMap c.directMap c.direct_mem) ≫
      a.directMap e.directMap e.direct_mem := by simp only [Category.assoc]
    _ = a.inverseMap d.inverseMap d.inverse_mem ≫
      (a.directMap d.directMap d.direct_mem ≫ a.inverseMap e.inverseMap e.inverse_mem) ≫
      a.directMap e.directMap e.direct_mem := by
        rw [← a.interchange d.directMap e.inverseMap d.direct_mem e.inverse_mem]
    _ = a.map f ≫ a.map g := by dsimp only [map, evaluate, d, e]; simp only [Category.assoc]

/-- The actual direct and inverse source maps form an ordinary functor on the entire Reedy
category. -/
def toFunctor : J ⥤ C where
  obj := a.obj
  map := a.map
  map_id := a.map_id
  map_comp := a.map_comp

/-- Every actual direct source map is unchanged in the assembled ordinary functor. -/
theorem toFunctor_direct {i j : J} (f : i ⟶ j) (hf : r.direct f) :
    a.toFunctor.map f = a.directMap f hf := a.map_direct f hf

/-- Every actual inverse source map is unchanged in the assembled ordinary functor. -/
theorem toFunctor_inverse {i j : J} (f : i ⟶ j) (hf : r.inverse f) :
    a.toFunctor.map f = a.inverseMap f hf := a.map_inverse f hf

end NormalFunctorData

end CategoryTheory.ReedyStructure

end ReedyPart2

section ReedyPart3

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {s : ObjectProperty J}

/-- Forgetting an actual full-source factorization keeps its entire original ordinary factor
record. -/
def forgetFactor {i j : s.FullSubcategory} {f : i ⟶ j}
    (a : ReedyFactorization (r.direct.inverseImage s.ι) (r.inverse.inverseImage s.ι) f) :
    ReedyFactorization r.direct r.inverse f.hom where
  Z := a.middle.obj
  i := a.inverseMap.hom
  p := a.directMap.hom
  hi := a.inverse_mem
  hp := a.direct_mem
  fac := congrArg (fun f => f.hom) a.fac

/-- An original ordinary factor record with its actual middle membership is a full-source factor
record. -/
def liftFactor {i j : s.FullSubcategory} {f : i ⟶ j}
    (a : ReedyFactorization r.direct r.inverse f.hom) (ha : s a.middle) :
    ReedyFactorization (r.direct.inverseImage s.ι) (r.inverse.inverseImage s.ι) f where
  Z := ⟨a.middle, ha⟩
  i := ObjectProperty.homMk a.inverseMap
  p := ObjectProperty.homMk a.directMap
  hi := a.inverse_mem
  hp := a.direct_mem
  fac := by apply ObjectProperty.hom_ext; exact a.fac

/-- Lifting an unchanged original full-source factor record recovers that complete record. -/
theorem liftFactor_forgetFactor {i j : s.FullSubcategory} {f : i ⟶ j}
    (a : ReedyFactorization (r.direct.inverseImage s.ι) (r.inverse.inverseImage s.ι) f) :
    r.liftFactor (r.forgetFactor a) a.middle.property = a := by
  cases a
  rfl

/-- Forgetting full-source membership is injective on the complete actual factor records. -/
theorem forgetFactor_injective {i j : s.FullSubcategory} {f : i ⟶ j} :
    Function.Injective (r.forgetFactor (s := s) (f := f)) := by
  intro a b h
  have hm : a.middle = b.middle :=
    ObjectProperty.FullSubcategory.ext (congrArg ReedyFactorization.middle h)
  have hi : HEq (r.forgetFactor a).inverseMap (r.forgetFactor b).inverseMap :=
    Eq.mp (congrArg (fun z => HEq (r.forgetFactor a).inverseMap z.inverseMap) h) HEq.rfl
  have hd : HEq (r.forgetFactor a).directMap (r.forgetFactor b).directMap :=
    Eq.mp (congrArg (fun z => HEq (r.forgetFactor a).directMap z.directMap) h) HEq.rfl
  cases a with
  | mk am ai ad af aim adm =>
    cases b with
    | mk bm bi bd bf bim bdm =>
      dsimp only [forgetFactor] at hm hi hd
      cases hm
      have hi' : ai = bi := by apply ObjectProperty.hom_ext; exact eq_of_heq hi
      have hd' : ad = bd := by apply ObjectProperty.hom_ext; exact eq_of_heq hd
      cases hi'
      cases hd'
      rfl

/-- A source closed under smaller-or-equal degree has the same genuine ordinary Reedy structure. -/
def restrict (hs : ∀ i, s i → ∀ j, r.degree j ≤ r.degree i → s j) :
    ReedyStructure s.FullSubcategory D :=
  mk (fun i => r.degree i.obj) (r.direct.inverseImage s.ι) (r.inverse.inverseImage s.ι)
    inferInstance inferInstance
    (fun f hf => r.direct_le f.hom hf) (fun f hf => r.inverse_le f.hom hf)
    (fun {i j} f hf he => by
      obtain ⟨e, hf'⟩ := r.direct_equal f.hom hf he
      have e' : i = j := ObjectProperty.FullSubcategory.ext e
      refine ⟨e', ?_⟩
      apply ObjectProperty.hom_ext
      cases e'
      simpa only [eqToHom_refl, ObjectProperty.FullSubcategory.id_hom] using hf')
    (fun {i j} f hf he => by
      obtain ⟨e, hf'⟩ := r.inverse_equal f.hom hf he
      have e' : i = j := ObjectProperty.FullSubcategory.ext e
      refine ⟨e', ?_⟩
      apply ObjectProperty.hom_ext
      cases e'
      simpa only [eqToHom_refl, ObjectProperty.FullSubcategory.id_hom] using hf')
    (fun {i j} f => r.liftFactor (r.factor f.hom)
      (hs i.obj i.property _ (r.middle_le_source f.hom)))
    (fun f a b => r.forgetFactor_injective
      (r.factor_unique f.hom (r.forgetFactor a) (r.forgetFactor b)))

/-- The restricted degree is the original supplied degree at the original object. -/
theorem restrict_degree (hs : ∀ i, s i → ∀ j, r.degree j ≤ r.degree i → s j)
    (i : s.FullSubcategory) : (r.restrict hs).degree i = r.degree i.obj := rfl

/-- The restricted canonical factor has exactly the original canonical middle object. -/
theorem restrict_factor_middle (hs : ∀ i, s i → ∀ j, r.degree j ≤ r.degree i → s j)
    {i j : s.FullSubcategory} (f : i ⟶ j) :
    ((r.restrict hs).factor f).middle.obj = (r.factor f.hom).middle := rfl

/-- The restricted canonical inverse factor is exactly the original inverse factor map. -/
theorem restrict_factor_inverse (hs : ∀ i, s i → ∀ j, r.degree j ≤ r.degree i → s j)
    {i j : s.FullSubcategory} (f : i ⟶ j) :
    ((r.restrict hs).factor f).inverseMap.hom = (r.factor f.hom).inverseMap := rfl

/-- The restricted canonical direct factor is exactly the original direct factor map. -/
theorem restrict_factor_direct (hs : ∀ i, s i → ∀ j, r.degree j ≤ r.degree i → s j)
    {i j : s.FullSubcategory} (f : i ⟶ j) :
    ((r.restrict hs).factor f).directMap.hom = (r.factor f.hom).directMap := rfl

/-- The complete source strictly below the supplied original degree. -/
abbrev belowObjects (d : D) : ObjectProperty J := fun i => r.degree i < d

/-- The complete source through the supplied original degree. -/
abbrev throughObjects (d : D) : ObjectProperty J := fun i => r.degree i ≤ d

/-- The full original lower-degree subcategory, including every original arrow between its
objects. -/
abbrev Below (d : D) := (r.belowObjects d).FullSubcategory

/-- The full original degree truncation, including every original arrow between its objects. -/
abbrev Through (d : D) := (r.throughObjects d).FullSubcategory

/-- The smaller-degree full source has its genuine original restricted Reedy structure. -/
def belowStructure (d : D) : ReedyStructure (r.Below d) D :=
  r.restrict (fun _ hi _ hj => hj.trans_lt hi)

/-- The full degree truncation has its genuine original restricted Reedy structure. -/
def throughStructure (d : D) : ReedyStructure (r.Through d) D :=
  r.restrict (fun _ hi _ hj => hj.trans hi)

end CategoryTheory.ReedyStructure

end ReedyPart3
