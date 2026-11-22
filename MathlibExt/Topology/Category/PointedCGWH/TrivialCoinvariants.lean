/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.DiscreteCoinvariants

/-!
# Balanced smash for a trivial acting monoid

When the acting monoid is subsingleton, the two balancing maps agree and the balanced smash is isomorphic to the discrete smash indexed by the group. The isomorphism preserves each generator, the left group action and maps of coefficient objects.
-/

set_option autoImplicit false
noncomputable section

universe u v wH wG

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PointedCGWH

variable (H : Type wH) (G : Type wG) [Monoid H] [Subsingleton H] [Group G]
variable (Z : PointedCGWH.{u, max v (max wH wG)})
variable (rho : H →* End Z) (iota : H →* G)

/-- For a trivial scalar monoid the two actual native balancing arrows coincide. -/
theorem nativeBalancing_eq_of_subsingleton :
    smashBalancingGroup.{u, v, wH, wG} H G Z iota =
      smashBalancingCoefficient.{u, v, wH, wG} H G Z rho := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  have ha : ga.2 = 1 := Subsingleton.elim _ _
  have hg := smashBalancingGroup_generator.{u, v, wH, wG} H G Z iota ga
  have hc := smashBalancingCoefficient_generator.{u, v, wH, wG} H G Z rho ga
  have hi : iota ga.2 = 1 := (congrArg iota ha).trans iota.map_one
  have hr : (rho ga.2).asHom = 𝟙 Z := by
    rw [ha, rho.map_one]
    rfl
  exact hg.trans (by simpa only [hi, mul_one, hr, Category.id_comp] using hc.symm)

variable [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
  (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)]

/-- The actual native quotient by a trivial scalar monoid is the original discrete smash. -/
def nativeBalancedTrivialIso :
    nativeBalancedSmash.{u, v, wH, wG} H G Z rho iota ≅
      discreteSmashObj.{u, max v (max wH wG), wG} G Z := by
  let _ : IsIso (coequalizer.π
      (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)) :=
    coequalizer.π_of_eq (nativeBalancing_eq_of_subsingleton H G Z rho iota)
  exact (asIso (coequalizer.π
    (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
    (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho))).symm

/-- The trivial quotient comparison retains every original native coefficient injection. -/
theorem nativeBalancedTrivialIso_generator (g : G) :
    nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g ≫
        (nativeBalancedTrivialIso H G Z rho iota).hom =
      discreteSmashIncl.{u, max v (max wH wG), wG} G Z g := by
  let _ : IsIso (coequalizer.π
      (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho)) :=
    coequalizer.π_of_eq (nativeBalancing_eq_of_subsingleton H G Z rho iota)
  change (discreteSmashIncl.{u, max v (max wH wG), wG} G Z g ≫
      (asIso (coequalizer.π
        (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho))).hom) ≫
      (asIso (coequalizer.π
        (smashBalancingGroup.{u, v, wH, wG} H G Z iota)
        (smashBalancingCoefficient.{u, v, wH, wG} H G Z rho))).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The trivial-quotient comparison retains the actual full target left action. -/
theorem nativeBalancedTrivialIso_left
    (k : G) :
    (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom ≫
        (nativeBalancedTrivialIso H G Z rho iota).hom =
      (nativeBalancedTrivialIso H G Z rho iota).hom ≫
        discreteSmashLeft.{u, max v (max wH wG), wG} G Z k := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro g
  let qg := nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g
  let qkg := nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota (k * g)
  let e := nativeBalancedTrivialIso H G Z rho iota
  let a := (nativeBalancedLeftAut.{u, v, wH, wG} H G Z rho iota k).asIso.hom
  let l := discreteSmashLeft.{u, max v (max wH wG), wG} G Z k
  let jg := discreteSmashIncl.{u, max v (max wH wG), wG} G Z g
  let jkg := discreteSmashIncl.{u, max v (max wH wG), wG} G Z (k * g)
  have ha : qg ≫ a = qkg :=
    nativeBalancedLeftAut_generator.{u, v, wH, wG} H G Z rho iota k g
  have he : qg ≫ e.hom = jg := nativeBalancedTrivialIso_generator H G Z rho iota g
  have hek : qkg ≫ e.hom = jkg :=
    nativeBalancedTrivialIso_generator H G Z rho iota (k * g)
  have hl : jg ≫ l = jkg := discreteSmashLeft_generator G Z k g
  have hleft : (qg ≫ a) ≫ e.hom = jkg :=
    (congrArg (fun f => f ≫ e.hom) ha).trans hek
  have hright : (qg ≫ e.hom) ≫ l = jkg :=
    (congrArg (fun f => f ≫ l) he).trans hl
  change qg ≫ (a ≫ e.hom) = qg ≫ (e.hom ≫ l)
  exact (Category.assoc _ _ _).symm.trans
    (hleft.trans (hright.symm.trans (Category.assoc _ _ _)))

/-- Coefficient morphisms commute with the original trivial-quotient comparison. -/
theorem nativeBalancedTrivialIso_naturality
    (Z' : PointedCGWH.{u, max v (max wH wG)}) (rho' : H →* End Z')
    (f : Z ⟶ Z') (hf : ∀ (a : H), (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
    [HasCoequalizer (smashBalancingGroup.{u, v, wH, wG} H G Z' iota)
      (smashBalancingCoefficient.{u, v, wH, wG} H G Z' rho')] :
    nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf ≫
        (nativeBalancedTrivialIso H G Z' rho' iota).hom =
      (nativeBalancedTrivialIso H G Z rho iota).hom ≫
        nativeSmashCoefficientMap.{u, max v (max wH wG), wG} G Z Z' f := by
  apply nativeBalanced_hom_ext.{u, v, wH, wG} H G Z rho iota
  intro g
  let qg := nativeBalancedGenerator.{u, v, wH, wG} H G Z rho iota g
  let qg' := nativeBalancedGenerator.{u, v, wH, wG} H G Z' rho' iota g
  let e := nativeBalancedTrivialIso H G Z rho iota
  let e' := nativeBalancedTrivialIso H G Z' rho' iota
  let m := nativeBalancedMap.{u, v, wH, wG} H G Z rho iota Z' rho' f hf
  let n := nativeSmashCoefficientMap.{u, max v (max wH wG), wG} G Z Z' f
  let jg := discreteSmashIncl.{u, max v (max wH wG), wG} G Z g
  let jg' := discreteSmashIncl.{u, max v (max wH wG), wG} G Z' g
  have hm : qg ≫ m = f ≫ qg' :=
    nativeBalancedMap_generator.{u, v, wH, wG} H G Z rho iota Z' rho' f hf g
  have he : qg ≫ e.hom = jg := nativeBalancedTrivialIso_generator H G Z rho iota g
  have he' : qg' ≫ e'.hom = jg' := nativeBalancedTrivialIso_generator H G Z' rho' iota g
  have hn : jg ≫ n = f ≫ jg' :=
    nativeSmashCoefficientMap_generator.{u, max v (max wH wG), wG} G Z Z' f g
  have hleft : (qg ≫ m) ≫ e'.hom = f ≫ jg' :=
    (congrArg (fun k => k ≫ e'.hom) hm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => f ≫ k) he'))
  have hright : (qg ≫ e.hom) ≫ n = f ≫ jg' :=
    (congrArg (fun k => k ≫ n) he).trans hn
  change qg ≫ (m ≫ e'.hom) = qg ≫ (e.hom ≫ n)
  exact (Category.assoc _ _ _).symm.trans
    (hleft.trans (hright.symm.trans (Category.assoc _ _ _)))

end PointedCGWH
