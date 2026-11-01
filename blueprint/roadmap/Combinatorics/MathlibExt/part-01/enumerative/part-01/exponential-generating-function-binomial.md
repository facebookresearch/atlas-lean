---
article_id: af_4c96bf5fc6fff287a2bae1f7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.exponentialGeneratingFunction_binomialTransform
---

# Binomial Transform Exponential Generating Function

The exponential generating function of a sequence's binomial transform is
its exponential generating function multiplied by `exp`.

`b` is the binomial transform of `a`, `A` its exponential generating
function, and the conclusion is the EGF of `b`. The formulation is pointwise:
it assumes convergence of the EGF of `a` only at the argument `t` under
consideration.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BinomialTransformExponentialGeneratingFunction](../../../../../../sources/v2/MathlibExt.md)
- Ayhan Dil, Veli Kurt, and Mehmet Cenkci, *Algorithms for Bernoulli and Related Polynomials*, Journal of Integer Sequences 10 (2007), Article 07.5.4, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex>, Proposition `prop2` (proof attributed to Seidel), lines 221-233; the binomial-transform relation `a_0^n = Σᵢ C(n,i) a_i^0` is equation (8)/(9), lines 188-199.
