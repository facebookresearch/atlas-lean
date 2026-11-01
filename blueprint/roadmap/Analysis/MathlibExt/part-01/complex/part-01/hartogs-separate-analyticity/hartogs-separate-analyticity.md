---
article_id: af_9dd71f027fd7fa3e8f04ddd5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.HartogsWanted.hartogs_separate_analyticity
---

# Hartogs separate analyticity

If `f : ℂⁿ → ℂ` is entire in each variable separately via `Function.update` slices, then `f` is
jointly `Differentiable ℂ` on `ℂⁿ`. Source: Hartogs separate analyticity (Osgood–Hartogs); see
Hörmander; Lean is scalar-valued entire separately holomorphic via Function.update slices implies
jointly Differentiable ℂ, finite-dimensional ℂⁿ specialization.

Proof: induction on the number of variables. Baire category gives a polydisc where `f` is
bounded, where Osgood's lemma makes it holomorphic; Hartogs' lemma on sub-mean-value functions
then makes the Cauchy expansion in the last variable converge locally uniformly.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Differentiable At uncurry of separately differentiable of locally bounded](differentiable-at-uncurry-of-separately-2.md)
- [Differentiable On cauchy Coefficient of separately differentiable of bounded](differentiable-on-cauchy-coefficient-of.md)
- [Hartogs eventually uniform of submean](hartogs-eventually-uniform-of-submean.md)
- [Hartogs pos Log norm le circle Average](hartogs-pos-log-norm-le-circle-average.md)
- [Norm cauchy Coefficient le](norm-cauchy-coefficient-le.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.HartogsSeparateAnalyticity](../../../../../../../sources/v2/MathlibExt.md)
