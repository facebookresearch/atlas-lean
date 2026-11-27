# Complete numerical-range inequality for matrices with constant two

Let $n,m$ be positive integers and $d\ge0$. For a complex $n$-by-$n$ matrix $A$ and arbitrary complex $m$-by-$m$ matrices $B_0,\ldots,B_d$, let $W(A)=\{\langle x,Ax\rangle:\|x\|_2=1\}$ with the inner product linear in the second argument. In Euclidean operator norms the claimed bound is

$$\left\|\sum_{k=0}^d A^k\otimes B_k\right\|\le2\sup_{z\in W(A)}\left\|\sum_{k=0}^d z^k B_k\right\|,$$

where $\otimes$ is the Kronecker matrix product in the indicated order. No normality or interior hypothesis is imposed. The combined comparator also asserts the [separate lower bound](two-le-of-uniform-complete-numerical-ran.md) $2\le c$ for any real uniform constant $c$ satisfying the same bound at all positive sizes and all degrees.

## Depends on

- [Numerical range](numerical-range.md) (conjugated to use the second-argument convention).

## Proof depends on

- The complete, not just scalar, upper-bound argument and its extension to numerical ranges with empty interior.

## Expansion

Isolate the complete norm estimate on a complex matrix polynomial calculus, including the arbitrary amplification dimension and positive size cases. The independent finite nilpotent obstruction to constants below two does not prove this upper bound.

## Sources

- OpenAI, [DirectCrouzeix comparator, complete_crouzeix](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectCrouzeix.lean#L34-L36).
- OpenAI, [CompleteCrouzeix comparator, main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CompleteCrouzeix.lean#L33-L35).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/325.md).
