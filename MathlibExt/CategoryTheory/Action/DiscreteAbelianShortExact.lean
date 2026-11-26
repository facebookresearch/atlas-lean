/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionAdjunction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Group.PUnit

/-!
# Short exactness detected on the underlying abelian groups

Let G be a group with a topology, with discrete coefficient groups in an independent universe.
The additive forgetful functor sends action morphisms to their additive maps. The one-element
group with trivial action is a zero object.

If a short complex A→B→C of discrete continuous actions becomes short exact after forgetting,
its first arrow is a kernel and its second a cokernel in the action category. The underlying
universal additive maps are equivariant and continuous because their sources are discrete. These
kernel and cokernel properties give zero homology data and prove short exactness of the same
action sequence.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable {G : Type g} [Group G] [TopologicalSpace G]

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. For parallel
action morphisms f,h, U(f+h)=U(f)+U(h), with pointwise addition on the same coefficient groups. -/
instance forget_additive : (forget.{g, w} G).Additive where
  map_add := by intro X Y f h; rfl

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. The trivial
G-action on the one-element abelian group in coefficient universe w defines this zero
coefficient action. -/
def discreteZero : DiscreteAbelianAction.{g, w} G :=
  trivialObject.{g, w} G (AddCommGrpCat.of PUnit.{w + 1})

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. The trivial
one-element action is a zero object: for every coefficient action A, its Hom sets to and from
that action contain only the zero morphism. -/
theorem discreteZero_isZero : IsZero (discreteZero.{g, w} (G := G)) := by
  let : Subsingleton (underlying (discreteZero.{g, w} (G := G))) :=
    (show Subsingleton PUnit.{w + 1} from inferInstance)
  let : Subsingleton ((forget.{g, w} G).obj (discreteZero.{g, w} (G := G))) :=
    (show Subsingleton PUnit.{w + 1} from inferInstance)
  constructor
  · intro A
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply (forget G).map_injective
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    exact hx ▸ map_zero (homToAdd f)
  · intro A
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply (forget G).map_injective
    ext x
    exact Subsingleton.elim _ _

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. For a short
complex S=(A --a→ B --b→ C) whose forgotten group sequence is short exact, a is a kernel of b.
Every k:D→B with k≫b=0 has a unique lift l:D→A with l≫a=k, and the underlying additive lift is
equivariant. -/
def isKernelOfForgetShortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, w} G))
    (hS : (S.map (forget.{g, w} G)).ShortExact) : IsLimit (KernelFork.ofι S.f S.zero) := by
  classical
  let T := S.map (forget.{g, w} G)
  have hf : Function.Injective (homToAdd S.f) := (AddCommGrpCat.mono_iff_injective T.f).mp hS.mono_f
  have hex : ∀ y : underlying S.X₂, homToAdd S.g y = 0 → ∃ x : underlying S.X₁,
      homToAdd S.f x = y :=
    T.ab_exact_iff.mp hS.exact
  let : Mono S.f := (forget G).mono_of_mono_map hS.mono_f
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  have hval (a : underlying A) : homToAdd S.g (homToAdd k a) = 0 := by
    have he := congrArg (fun f : A ⟶ S.X₃ => homToAdd f a) hk
    exact he
  let lift (a : underlying A) := Classical.choose (hex (homToAdd k a) (hval a))
  have lift_spec (a : underlying A) : homToAdd S.f (lift a) = homToAdd k a :=
    Classical.choose_spec (hex (homToAdd k a) (hval a))
  let phi : underlying A →+ underlying S.X₁ :=
    { toFun := lift
      map_zero' := hf (by rw [lift_spec, map_zero, map_zero])
      map_add' := fun a b => hf (by rw [lift_spec, map_add, map_add, lift_spec, lift_spec]) }
  let ell : A ⟶ S.X₁ := ofAddHom ⟨phi, fun g a => hf (by
    change homToAdd S.f (lift (g • a)) = homToAdd S.f (g • lift a)
    rw [lift_spec, homToAdd_equivariant, homToAdd_equivariant, lift_spec])⟩
  refine ⟨ell, ?_⟩
  apply (forget G).map_injective
  ext a
  exact lift_spec a

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. If U(S) is
short exact for S=(A --a→ B --b→ C), then b is a cokernel of a. Every k:B→D with a≫k=0 descends
uniquely to l:C→D with b≫l=k. The quotient descent is an equivariant additive action map. -/
def isCokernelOfForgetShortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, w} G))
    (hS : (S.map (forget.{g, w} G)).ShortExact) : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  classical
  let T := S.map (forget.{g, w} G)
  have hq : Function.Surjective (homToAdd S.g) := (AddCommGrpCat.epi_iff_surjective T.g).mp hS.epi_g
  have hex : ∀ y : underlying S.X₂, homToAdd S.g y = 0 → ∃ x : underlying S.X₁,
      homToAdd S.f x = y :=
    T.ab_exact_iff.mp hS.exact
  let : Epi S.g := (forget G).epi_of_epi_map hS.epi_g
  apply CokernelCofork.IsColimit.ofπ'
  intro A k hk
  have hker (y : underlying S.X₂) (hy : homToAdd S.g y = 0) : homToAdd k y = 0 := by
    obtain ⟨x, rfl⟩ := hex y hy
    exact congrArg (fun f : S.X₁ ⟶ A => homToAdd f x) hk
  have hsame (y z : underlying S.X₂) (h : homToAdd S.g y = homToAdd S.g z) :
      homToAdd k y = homToAdd k z := by
    have hz : homToAdd k (y - z) = 0 := hker (y - z) (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at hz
  let s (z : underlying S.X₃) := Classical.choose (hq z)
  have hs (z : underlying S.X₃) : homToAdd S.g (s z) = z := Classical.choose_spec (hq z)
  let phi : underlying S.X₃ →+ underlying A :=
    { toFun := fun z => homToAdd k (s z)
      map_zero' := (hsame (s 0) 0 (by rw [hs, map_zero])).trans (map_zero _)
      map_add' := fun a b => (hsame (s (a + b)) (s a + s b)
        (by rw [hs, map_add, hs, hs])).trans (map_add _ _ _) }
  let ell : S.X₃ ⟶ A := ofAddHom ⟨phi, fun g z =>
    (hsame (s (g • z)) (g • s z) (by rw [hs, homToAdd_equivariant, hs])).trans
      (homToAdd_equivariant k g (s z))⟩
  refine ⟨ell, ?_⟩
  apply (forget G).map_injective
  ext y
  exact hsame (s (homToAdd S.g y)) y (hs _)

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. For S=(A --a→
B --b→ C) with U(S) short exact, the kernel a and cokernel b give left and right homology data
whose common homology object is the trivial one-element action. This is homology data for the
given short complex. -/
def homologyDataOfForgetShortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, w} G))
    (hS : (S.map (forget.{g, w} G)).ShortExact) : S.HomologyData := by
  let Z := discreteZero.{g, w} (G := G)
  have hZ : IsZero Z := discreteZero_isZero.{g, w} (G := G)
  let hk := isKernelOfForgetShortExact S hS
  let hq := isCokernelOfForgetShortExact S hS
  have hkId : hk.lift (KernelFork.ofι S.f S.zero) = 𝟙 S.X₁ := by
    apply Fork.IsLimit.hom_ext hk
    change hk.lift (KernelFork.ofι S.f S.zero) ≫ S.f = (𝟙 S.X₁) ≫ S.f
    exact (hk.fac (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero).trans
      (Category.id_comp S.f).symm
  have hqId : hq.desc (CokernelCofork.ofπ S.g S.zero) = 𝟙 S.X₃ := by
    apply Cofork.IsColimit.hom_ext hq
    change S.g ≫ hq.desc (CokernelCofork.ofπ S.g S.zero) = S.g ≫ (𝟙 S.X₃)
    exact (hq.fac (CokernelCofork.ofπ S.g S.zero) WalkingParallelPair.one).trans
      (Category.comp_id S.g).symm
  let L : S.LeftHomologyData :=
    { K := S.X₁
      H := Z
      i := S.f
      π := 0
      wi := S.zero
      hi := hk
      wπ := HasZeroMorphisms.comp_zero _ _
      hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by rw [hkId]; infer_instance) hZ }
  let Q : S.RightHomologyData :=
    { Q := S.X₃
      H := Z
      p := S.g
      ι := 0
      wp := S.zero
      hp := hq
      wι := HasZeroMorphisms.zero_comp _ _
      hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by rw [hqId]; infer_instance) hZ }
  exact
    { left := L
      right := Q
      iso := Iso.refl Z
      comm := by change (0 : S.X₁ ⟶ Z) ≫ (𝟙 Z) ≫ (0 : Z ⟶ S.X₃) = S.f ≫ S.g
                 simp only [HasZeroMorphisms.zero_comp]
                 exact S.zero.symm }

/-- Let G be a group with a topology in universe g and discrete continuous abelian actions have
coefficient universe w, independently. Let U forget the action to abelian groups. For a short
complex S, if U(S) is short exact, then S is short exact in the action category. The first and
second arrows satisfy the kernel and cokernel universal properties, and their underlying
injectivity and surjectivity imply monicity and epicity. -/
theorem shortExact_of_forget_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, w} G))
    (hS : (S.map (forget.{g, w} G)).ShortExact) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine ⟨⟨homologyDataOfForgetShortExact S hS, ?_⟩⟩
    change IsZero (discreteZero.{g, w} (G := G))
    exact discreteZero_isZero.{g, w} (G := G)
  · exact (forget G).mono_of_mono_map hS.mono_f
  · exact (forget G).epi_of_epi_map hS.epi_g

end CategoryTheory.DiscreteAbelianAction
