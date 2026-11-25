/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.ZeroDifferentialHomology
public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.Cycles
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Flat
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Basic.UnivLE

/-!
# Connecting maps for balanced tensor cycles and images

The short exact cycles, term and outgoing-image tensor sequence has its native
homology connecting map. In the zero-differential homology coordinates, it sends
an image coefficient in degree p to its boundary inclusion in cycles degree p - 1.
The horizontal differential has positive sign; the signed vertical term vanishes
on an actual cycle of the second complex.

Exactness is required only of the first complex's coefficient tensor functors
and its outgoing images. The second complex may have nonzero differentials and
nonflat terms. Native lifts give the same comparison for independent input worlds
and any common lift height.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace ChainComplex.BalancedTensor

universe u v w t

local notation "c" => ComplexShape.down ℤ

private def integerMap (A : AddCommGrpCat.{v}) (a : A) :
    AddCommGrpCat.of (ULift.{v} ℤ) ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun z => z.down • a
      map_zero' := by change (0 : ℤ) • a = 0; exact zero_zsmul a
      map_add' := fun x y => by
        change (x.down + y.down) • a = x.down • a + y.down • a
        exact add_zsmul a x.down y.down }

private theorem integerMap_comp {A B : AddCommGrpCat.{v}} (a : A) (f : A ⟶ B) :
    integerMap A a ≫ f = integerMap B (f.hom a) := by
  apply ConcreteCategory.ext_apply
  intro z
  change f.hom (z.down • a) = z.down • f.hom a
  exact f.hom.map_zsmul z.down a

private theorem integerMap_zero (A : AddCommGrpCat.{v}) : integerMap A 0 = 0 := by
  apply ConcreteCategory.ext_apply
  intro z
  change z.down • (0 : A) = 0
  exact smul_zero z.down

private theorem integerMap_one (A : AddCommGrpCat.{v}) (a : A) :
    (integerMap A a).hom (ULift.up 1) = a := by
  change (1 : ℤ) • a = a
  exact one_zsmul a

private theorem integerMap_liftCycles
    (K : ChainComplex AddCommGrpCat.{v} ℤ) (i j : ℤ) (hj : c.next i = j)
    (z : K.cycles i)
    (hz : integerMap (K.X i) ((K.iCycles i).hom z) ≫ K.d i j = 0) :
    K.liftCycles (integerMap (K.X i) ((K.iCycles i).hom z)) j hj hz =
      integerMap (K.cycles i) z := by
  apply (cancel_mono (K.iCycles i)).1
  rw [HomologicalComplex.liftCycles_i, integerMap_comp]

private theorem connecting_apply_of_lift
    {S : ShortComplex (ChainComplex AddCommGrpCat.{v} ℤ)} (hS : S.ShortExact)
    (i j : ℤ) (hij : c.Rel i j) (z₃ : S.X₃.cycles i) (b : S.X₂.X i)
    (z₁ : S.X₁.cycles j)
    (hb : (S.g.f i).hom b = (S.X₃.iCycles i).hom z₃)
    (hd : (S.X₂.d i j).hom b = (S.f.f j).hom ((S.X₁.iCycles j).hom z₁)) :
    (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom z₃) =
      (S.X₁.homologyπ j).hom z₁ := by
  let a₃ := integerMap (S.X₃.X i) ((S.X₃.iCycles i).hom z₃)
  let a₂ := integerMap (S.X₂.X i) b
  let a₁ := integerMap (S.X₁.X j) ((S.X₁.iCycles j).hom z₁)
  have hz₃ : a₃ ≫ S.X₃.d i j = 0 := by
    change integerMap (S.X₃.X i) ((S.X₃.iCycles i).hom z₃) ≫ S.X₃.d i j = 0
    rw [integerMap_comp]
    have hzero : (S.X₃.d i j).hom ((S.X₃.iCycles i).hom z₃) = 0 :=
      ConcreteCategory.congr_hom (S.X₃.iCycles_d i j) z₃
    rw [hzero, integerMap_zero]
  have h₂ : a₂ ≫ S.g.f i = a₃ := by
    change integerMap (S.X₂.X i) b ≫ S.g.f i = _
    rw [integerMap_comp]
    exact congrArg (integerMap (S.X₃.X i)) hb
  have h₁ : a₁ ≫ S.f.f j = a₂ ≫ S.X₂.d i j := by
    change integerMap (S.X₁.X j) ((S.X₁.iCycles j).hom z₁) ≫ S.f.f j =
      integerMap (S.X₂.X i) b ≫ S.X₂.d i j
    rw [integerMap_comp, integerMap_comp]
    exact congrArg (integerMap (S.X₂.X j)) hd.symm
  have h := hS.δ_eq i j hij a₃ hz₃ a₂ h₂ a₁ h₁ (c.next j) rfl
  dsimp only [a₃, a₁] at h
  rw [integerMap_liftCycles, integerMap_liftCycles] at h
  have hpoint := ConcreteCategory.congr_hom h (ULift.up 1)
  simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, integerMap_one] using hpoint

private theorem down_rel_next (i : ℤ) : c.Rel i (c.next i) := by
  have h : c.Rel i (i - 1) := by
    change i - 1 + 1 = i
    exact sub_add_cancel i 1
  simpa only [c.next_eq' h] using h

private theorem next_add_eq (p q n : ℤ) (h : p + q = n) : c.next p + q = n - 1 := by
  have hn := c.next_eq' (show c.Rel p (p - 1) by
    change p - 1 + 1 = p
    exact sub_add_cancel p 1)
  rw [hn]
  omega

variable (R : Type u) [Ring R]

private theorem d_mk_rel
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p p' q q' n n' : ℤ) (hp : c.Rel p p') (hq : c.Rel q q') (hn : c.Rel n n')
    (h : p + q = n) (h₁ : p' + q = n') (h₂ : p + q' = n')
    (x : P.X p) (y : Q.X q) :
    ((complex R P Q).d n n').hom (mk R P Q p q n h x y) =
      mk R P Q p' q n' h₁ ((P.d p p').hom x) y +
        p.negOnePow • mk R P Q p q' n' h₂ x ((Q.d q q').hom y) := by
  have hp' : p' = p - 1 := by change p' + 1 = p at hp; omega
  have hq' : q' = q - 1 := by change q' + 1 = q at hq; omega
  have hn' : n' = n - 1 := by change n' + 1 = n at hn; omega
  subst p'
  subst q'
  subst n'
  exact d_mk R P Q p q n h x y

private theorem mk_zero_right
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) :
    mk R P Q p q n h x 0 = 0 := by
  dsimp only [mk]
  simp only [TensorProduct.Balanced.mk_apply, TensorProduct.tmul_zero, map_zero]

/-- The actual outgoing image family, retaining its native degrees. -/
abbrev connectingImages (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    ℤ → ModuleCat.{v} Rᵐᵒᵖ :=
  fun p => (HomologicalComplex.outgoingImageZeroComplex P).X p

/-- The actual cycles family of the original right complex. -/
abbrev connectingCycles (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    ℤ → ModuleCat.{v} Rᵐᵒᵖ :=
  P.cycles

section Resolutions

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]
variable (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)

section ImageExact

variable [∀ p : ℤ,
  ((ModuleCat.BalancedTensor.groupBifunctor R).obj (connectingImages R P p)).PreservesHomology]

/-- Exact image coefficient functors earn the short exact sequence of tensor totals. -/
theorem cyclesTensorSequence_shortExact_of_exactImages :
    (cyclesTensorSequence R P Q).ShortExact := by
  apply cyclesTensorSequence_shortExact R P Q
  intro i B
  exact (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
    R (connectingImages R P i)).1
      (Functor.preservesFiniteLimits_of_preservesHomology
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj (connectingImages R P i))) B

/-- The native homology connecting map of the earned cycles/image tensor sequence. -/
def cyclesTensorConnecting (n : ℤ) :
    (cyclesTensorSequence R P Q).X₃.homology n ⟶
      (cyclesTensorSequence R P Q).X₁.homology (n - 1) :=
  (cyclesTensorSequence_shortExact_of_exactImages R P Q).δ n (n - 1)
    (by change n - 1 + 1 = n; exact sub_add_cancel n 1)

/-- Image coefficients tensored with homology of the unchanged second complex. -/
abbrev connectingImageHomologyFamily (n : ℤ) :=
  zeroDifferentialTensorHomologyFamily R (connectingImages R P) Q n

/-- The canonical full image-tensor homology comparison. -/
def connectingImageHomologyIso (n : ℤ) :
    (∐ connectingImageHomologyFamily R P Q n) ≅
      (cyclesTensorSequence R P Q).X₃.homology n := by
  change (∐ zeroDifferentialTensorHomologyFamily R (connectingImages R P) Q n) ≅
    (complex R (zeroDifferentialComplex R (connectingImages R P)) Q).homology n
  exact zeroDifferentialTensorHomologyIso R (connectingImages R P) Q n

section TermExact

variable [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X p)).PreservesHomology]

/-- Exact terms and images give exact coefficient functors on actual cycles. -/
theorem connectingCycles_preservesHomology (i : ℤ) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles i)).PreservesHomology := by
  let hP : ∀ j B, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.X j)).obj B) :=
    fun j B => (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (P.X j)).1 (Functor.preservesFiniteLimits_of_preservesHomology
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X j))) B
  let hI : ∀ j B, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d j (c.next j)))).obj B) :=
    fun j B => (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (connectingImages R P j)).1 (Functor.preservesFiniteLimits_of_preservesHomology
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj (connectingImages R P j))) B
  let F := (ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles i)
  let : PreservesFiniteLimits F :=
    (ModuleCat.BalancedTensor.groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
      R (P.cycles i)).2 (ModuleCat.BalancedTensor.isZero_torFirst_one_cycles R P hP hI i)
  let : PreservesFiniteColimits F := inferInstance
  exact ((Functor.exact_tfae F).out 4 3).1 ⟨inferInstance, inferInstance⟩

/-- The full cycles-tensor homology family. -/
abbrev connectingCyclesHomologyFamily (n : ℤ) :=
  zeroDifferentialTensorHomologyFamily R (connectingCycles R P) Q n

/-- The canonical full cycles-tensor homology comparison. -/
def connectingCyclesHomologyIso (n : ℤ) :
    (∐ connectingCyclesHomologyFamily R P Q n) ≅
      (cyclesTensorSequence R P Q).X₁.homology n := by
  let : ∀ i : ℤ,
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles i)).PreservesHomology :=
    connectingCycles_preservesHomology R P
  change (∐ zeroDifferentialTensorHomologyFamily R (connectingCycles R P) Q n) ≅
    (complex R (zeroDifferentialComplex R (connectingCycles R P)) Q).homology n
  exact zeroDifferentialTensorHomologyIso R (connectingCycles R P) Q n

/-- The positive connecting formula on the original image coefficient and actual cycle. -/
theorem cyclesTensorConnecting_mk (p q n : ℤ) (h : p + q = n)
    (x : connectingImages R P p) (y : Q.cycles q) :
    letI : Module ℤ (Q.cycles q) := Module.compHom (Q.cycles q) (algebraMap ℤ R)
    letI : Module ℤ (Q.homology q) := Module.compHom (Q.homology q) (algebraMap ℤ R)
    (Sigma.ι (connectingImageHomologyFamily R P Q n) ⟨(p, q), h⟩ ≫
        (connectingImageHomologyIso R P Q n).hom ≫ cyclesTensorConnecting R P Q n).hom
          (TensorProduct.Balanced.mk ℤ R (connectingImages R P p) (Q.homology q)
            x ((Q.homologyπ q).hom y)) =
      (Sigma.ι (connectingCyclesHomologyFamily R P Q (n - 1))
          ⟨(c.next p, q), by
            have hp : c.Rel p (p - 1) := by
              change p - 1 + 1 = p
              exact sub_add_cancel p 1
            rw [c.next_eq' hp]
            omega⟩ ≫
        (connectingCyclesHomologyIso R P Q (n - 1)).hom).hom
          (TensorProduct.Balanced.mk ℤ R (P.cycles (c.next p)) (Q.homology q)
            ((HomologicalComplex.boundaryCyclesMap P p (c.next p)).hom x)
              ((Q.homologyπ q).hom y)) := by
  letI : Module ℤ (Q.cycles q) := Module.compHom (Q.cycles q) (algebraMap ℤ R)
  letI : Module ℤ (Q.homology q) := Module.compHom (Q.homology q) (algebraMap ℤ R)
  let : ∀ i : ℤ,
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles i)).PreservesHomology :=
    connectingCycles_preservesHomology R P
  let S := cyclesTensorSequence R P Q
  let hS : S.ShortExact := cyclesTensorSequence_shortExact_of_exactImages R P Q
  let β := HomologicalComplex.boundaryCyclesMap P p (c.next p)
  let yy : Q.X q := (Q.iCycles q).hom y
  obtain ⟨z₃, hz₃, hc₃⟩ :=
    zeroDifferentialTensorHomologyIso_mk R (connectingImages R P) Q p q n h x y
  obtain ⟨z₁, hz₁, hc₁⟩ :=
    zeroDifferentialTensorHomologyIso_mk R (connectingCycles R P) Q
      (c.next p) q (n - 1) (next_add_eq p q n h) (β.hom x) y
  let a : P.X p := Classical.choose
    ((ModuleCat.epi_iff_surjective (Abelian.factorThruImage (P.d p (c.next p)))).1
      inferInstance x)
  have ha : (Abelian.factorThruImage (P.d p (c.next p))).hom a = x :=
    Classical.choose_spec
      ((ModuleCat.epi_iff_surjective (Abelian.factorThruImage (P.d p (c.next p)))).1
        inferInstance x)
  let b : S.X₂.X n := mk R P Q p q n h a yy
  have hb : (S.g.f n).hom b = (S.X₃.iCycles n).hom z₃ := by
    change ((map R (HomologicalComplex.cyclesComplexProjection.app P) (𝟙 Q)).f n).hom
        (mk R P Q p q n h a yy) = _
    rw [map_mk]
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    change mk R (HomologicalComplex.outgoingImageZeroComplex P) Q p q n h
      ((Abelian.factorThruImage (P.d p (c.next p))).hom a) yy = _
    rw [ha]
    exact hz₃.symm
  have hdP : (P.d p (c.next p)).hom a = (P.iCycles (c.next p)).hom (β.hom x) := by
    have hf := ConcreteCategory.congr_hom (Abelian.image.fac (P.d p (c.next p))) a
    have hbβ := ConcreteCategory.congr_hom
      (HomologicalComplex.boundaryCyclesMap_i P p (c.next p)) x
    exact hf.symm.trans ((congrArg (Abelian.image.ι (P.d p (c.next p))).hom ha).trans hbβ.symm)
  have hQ : (Q.d q (c.next q)).hom yy = 0 :=
    ConcreteCategory.congr_hom (Q.iCycles_d q (c.next q)) y
  have hdiff : (S.X₂.d n (n - 1)).hom b =
      mk R P Q (c.next p) q (n - 1) (next_add_eq p q n h)
        ((P.iCycles (c.next p)).hom (β.hom x)) yy := by
    have hn : c.Rel n (n - 1) := by
      change n - 1 + 1 = n
      exact sub_add_cancel n 1
    have hh := d_mk_rel R P Q p (c.next p) q (c.next q) n (n - 1)
      (down_rel_next p) (down_rel_next q) hn h (next_add_eq p q n h)
      (by have hq := next_add_eq q p n (by simpa only [add_comm] using h); omega) a yy
    change ((complex R P Q).d n (n - 1)).hom (mk R P Q p q n h a yy) = _
    rw [hh, hQ, mk_zero_right, smul_zero, add_zero, hdP]
  have hfirst : (S.f.f (n - 1)).hom ((S.X₁.iCycles (n - 1)).hom z₁) =
      mk R P Q (c.next p) q (n - 1) (next_add_eq p q n h)
        ((P.iCycles (c.next p)).hom (β.hom x)) yy := by
    rw [hz₁]
    change ((map R (HomologicalComplex.cyclesComplexInclusion.app P) (𝟙 Q)).f (n - 1)).hom
      (mk R (HomologicalComplex.cyclesZeroComplex P) Q
        (c.next p) q (n - 1) (next_add_eq p q n h) (β.hom x) yy) = _
    rw [map_mk]
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    rfl
  have hδ := connecting_apply_of_lift hS n (n - 1)
    (by change n - 1 + 1 = n; exact sub_add_cancel n 1) z₃ b z₁ hb
      (hdiff.trans hfirst.symm)
  change (cyclesTensorConnecting R P Q n).hom
      ((Sigma.ι (connectingImageHomologyFamily R P Q n) ⟨(p, q), h⟩ ≫
        (connectingImageHomologyIso R P Q n).hom).hom _) = _
  rw [hc₃]
  exact hδ.trans hc₁.symm

/-- The connecting map is the boundary inclusion in the full homology-tensor coordinates. -/
theorem cyclesTensorConnecting_square (p q n : ℤ) (h : p + q = n) :
    Sigma.ι (connectingImageHomologyFamily R P Q n) ⟨(p, q), h⟩ ≫
        (connectingImageHomologyIso R P Q n).hom ≫ cyclesTensorConnecting R P Q n =
      ((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P p (c.next p))).app (Q.homology q) ≫
        Sigma.ι (connectingCyclesHomologyFamily R P Q (n - 1))
          ⟨(c.next p, q), by
            have hp : c.Rel p (p - 1) := by
              change p - 1 + 1 = p
              exact sub_add_cancel p 1
            rw [c.next_eq' hp]
            omega⟩ ≫
          (connectingCyclesHomologyIso R P Q (n - 1)).hom := by
  letI : Module ℤ (Q.homology q) := Module.compHom (Q.homology q) (algebraMap ℤ R)
  apply ConcreteCategory.ext_apply
  intro z
  obtain ⟨a, rfl⟩ :=
    Submodule.mkQ_surjective (TensorProduct.balanceRelations ℤ R (connectingImages R P p)
      (Q.homology q)) z
  refine TensorProduct.inductionOn a ?_ ?_
  · intro x m
    obtain ⟨y, hy⟩ := ((ModuleCat.epi_iff_surjective (Q.homologyπ q)).1 inferInstance) m
    subst m
    let β := HomologicalComplex.boundaryCyclesMap P p (c.next p)
    have hMap :
        (((ModuleCat.BalancedTensor.groupBifunctor R).map β).app (Q.homology q)).hom
          (TensorProduct.Balanced.mk ℤ R (connectingImages R P p) (Q.homology q)
            x ((Q.homologyπ q).hom y)) =
        TensorProduct.Balanced.mk ℤ R (P.cycles (c.next p)) (Q.homology q)
          (β.hom x) ((Q.homologyπ q).hom y) :=
      ModuleCat.BalancedTensor.groupBifunctor_map_mk R β (Q.homology q)
        x ((Q.homologyπ q).hom y)
    change (Sigma.ι (connectingImageHomologyFamily R P Q n) ⟨(p, q), h⟩ ≫
        (connectingImageHomologyIso R P Q n).hom ≫ cyclesTensorConnecting R P Q n).hom
          (TensorProduct.Balanced.mk ℤ R (connectingImages R P p) (Q.homology q)
            x ((Q.homologyπ q).hom y)) =
      (Sigma.ι (connectingCyclesHomologyFamily R P Q (n - 1))
          ⟨(c.next p, q), next_add_eq p q n h⟩ ≫
        (connectingCyclesHomologyIso R P Q (n - 1)).hom).hom
          ((((ModuleCat.BalancedTensor.groupBifunctor R).map β).app (Q.homology q)).hom
            (TensorProduct.Balanced.mk ℤ R (connectingImages R P p) (Q.homology q)
              x ((Q.homologyπ q).hom y)))
    rw [hMap]
    exact cyclesTensorConnecting_mk R P Q p q n h x y
  · intro a b ha hb
    simp only [map_add, ha, hb]

end TermExact
end ImageExact
end Resolutions

/-- Lift the actual right complex to a common carrier universe, retaining every map. -/
abbrev connectingRightAt
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) :
    ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
  ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P

/-- Lift the independent left complex by the same native functor. -/
abbrev connectingLeftAt
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) :
    ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
  ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex c).obj Q

section Lifted

variable (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{w} R) ℤ)
variable [∀ p : ℤ,
  ((ModuleCat.BalancedTensor.groupBifunctor R).obj
    (connectingImages R (connectingRightAt.{u, v, w, t} R P) p)).PreservesHomology]

/-- The native connecting map with independent input worlds and arbitrary lift height. -/
def cyclesTensorConnectingAt (n : ℤ) :
    (cyclesTensorSequence R (connectingRightAt.{u, v, w, t} R P)
      (connectingLeftAt.{u, v, w, t} R Q)).X₃.homology n ⟶
    (cyclesTensorSequence R (connectingRightAt.{u, v, w, t} R P)
      (connectingLeftAt.{u, v, w, t} R Q)).X₁.homology (n - 1) :=
  cyclesTensorConnecting R (connectingRightAt.{u, v, w, t} R P)
    (connectingLeftAt.{u, v, w, t} R Q) n

variable [∀ p : ℤ,
  ((ModuleCat.BalancedTensor.groupBifunctor R).obj
    ((connectingRightAt.{u, v, w, t} R P).X p)).PreservesHomology]

/-- The full connecting square in the actual common universe of both native lifts. -/
theorem cyclesTensorConnecting_squareAt (p q n : ℤ) (h : p + q = n) :
    Sigma.ι (connectingImageHomologyFamily R (connectingRightAt.{u, v, w, t} R P)
      (connectingLeftAt.{u, v, w, t} R Q) n) ⟨(p, q), h⟩ ≫
      (connectingImageHomologyIso R (connectingRightAt.{u, v, w, t} R P)
        (connectingLeftAt.{u, v, w, t} R Q) n).hom ≫ cyclesTensorConnectingAt.{u, v, w, t} R P Q n =
    ((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap (connectingRightAt.{u, v, w, t} R P)
        p (c.next p))).app ((connectingLeftAt.{u, v, w, t} R Q).homology q) ≫
      Sigma.ι (connectingCyclesHomologyFamily R (connectingRightAt.{u, v, w, t} R P)
        (connectingLeftAt.{u, v, w, t} R Q) (n - 1))
        ⟨(c.next p, q), by
          have hp : c.Rel p (p - 1) := by
            change p - 1 + 1 = p
            exact sub_add_cancel p 1
          rw [c.next_eq' hp]
          omega⟩ ≫
        (connectingCyclesHomologyIso R (connectingRightAt.{u, v, w, t} R P)
          (connectingLeftAt.{u, v, w, t} R Q) (n - 1)).hom :=
  cyclesTensorConnecting_square R (connectingRightAt.{u, v, w, t} R P)
    (connectingLeftAt.{u, v, w, t} R Q) p q n h

end Lifted

end ChainComplex.BalancedTensor
