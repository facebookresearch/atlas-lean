/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi

/-! Exact integral spin numerators for the ninth prototype's nine original factors.
The four original Gaussians each retain their denominator eight. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The forward original Parker lift evaluates its phase at the inverse code label. -/
def generatedNinthIntegerPermutation (k : Fin 2) (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun n =>
  let t := (monsterSourcePermutationCode k).symm (golayLabelCoefficients n)
  nortonUIntegerSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) t) *
    v (nortonUIntegerLabel t)

/-- The integral forward operator is exactly the actual source permutation spin lift. -/
theorem generatedNinth_integer_permutation_embed (k : Fin 2) (v : NortonUIntegerVector) :
    (monsterSourcePermutationSpin k).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedNinthIntegerPermutation k v) := by
  ext t
  change qSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k)
      ((monsterSourcePermutationCode k).symm t)) *
    nortonUIntegerEmbed v ((monsterSourcePermutationCode k).symm t) = _
  simp only [nortonUIntegerEmbed, generatedNinthIntegerPermutation,
    nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

/-- Integer composition follows the literal nine-factor local word. -/
def generatedNinthIntegerSpin (v : NortonUIntegerVector) : NortonUIntegerVector :=
  nortonUIntegerXi (nortonUIntegerXi (generatedNinthIntegerPermutation 1
    (generatedNinthIntegerPermutation 0 (nortonUIntegerXi
      (generatedNinthIntegerPermutation 1 (generatedNinthIntegerPermutation 0
        (nortonUIntegerXi (generatedNinthIntegerPermutation 1 v))))))))

private theorem generatedNinth_spin_mul_apply (g h : SpinHolomorph) (v : SpinSpace) :
    (g * h).val v = g.val (h.val v) := rfl

private theorem generatedNinth_nine_spin_embed
    (s0 s1 sx : SpinHolomorph) (f0 f1 fx : NortonUIntegerVector → NortonUIntegerVector)
    (h0 : ∀ v, s0.val (nortonUIntegerEmbed v) = nortonUIntegerEmbed (f0 v))
    (h1 : ∀ v, s1.val (nortonUIntegerEmbed v) = nortonUIntegerEmbed (f1 v))
    (hx : ∀ v, sx.val (nortonUIntegerEmbed v) = (1 / 8 : ℝ) • nortonUIntegerEmbed (fx v))
    (v : NortonUIntegerVector) :
    (sx * sx * s1 * s0 * sx * s1 * s0 * sx * s1).val (nortonUIntegerEmbed v) =
      (1 / 4096 : ℝ) •
        nortonUIntegerEmbed (fx (fx (f1 (f0 (fx (f1 (f0 (fx (f1 v))))))))) := by
  simp only [generatedNinth_spin_mul_apply, h0, h1, hx, map_smul, smul_smul]
  norm_num

/-- Dividing the integer word by 4096 gives the genuine ninth spin operator. -/
theorem generatedNinth_integer_spin_embed (v : NortonUIntegerVector) :
    generatedNinthLocalFiber.val.1.val (nortonUIntegerEmbed v) =
      (1 / 4096 : ℝ) • nortonUIntegerEmbed (generatedNinthIntegerSpin v) := by
  have hf : generatedNinthLocalFiber.val.1 =
      xiSpinHolomorph * xiSpinHolomorph * monsterSourcePermutationSpin 1 *
        monsterSourcePermutationSpin 0 * xiSpinHolomorph * monsterSourcePermutationSpin 1 *
        monsterSourcePermutationSpin 0 * xiSpinHolomorph * monsterSourcePermutationSpin 1 := rfl
  rw [hf]
  exact generatedNinth_nine_spin_embed _ _ _ _ _ _
    (generatedNinth_integer_permutation_embed 0)
    (generatedNinth_integer_permutation_embed 1) nortonUIntegerXi_embed v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
