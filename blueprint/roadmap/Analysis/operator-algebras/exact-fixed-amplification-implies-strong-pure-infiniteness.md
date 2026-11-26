# A fixed proper-infinite amplification implies strong pure infiniteness under exactness

In an exact possibly nonunital complex C*-algebra $A$ with the star order, suppose there is one integer $n\ge1$ for which the $n$-copy diagonal of every nonzero positive element is properly infinite in the rectangular matrix comparison sense. Then for all positive $a,b$ and every $\epsilon>0$ there are $s,t\in A$ satisfying

$$\|s^*a^2s-a^2\|<\epsilon,\qquad \|t^*b^2t-b^2\|<\epsilon,\qquad \|s^*ab t\|<\epsilon.$$

## Depends on

- [Exactness and fixed-amplification conventions](exact-fixed-amplification-implies-individual-proper-infiniteness.md).

## Proof depends on

- [Proper infiniteness of each positive corner under exactness](exact-fixed-amplification-implies-individual-proper-infiniteness.md).
- [Diagonalization under individual proper infiniteness](individual-proper-infiniteness-implies-diagonalization.md), after bridging the two comparison models.

## Expansion

Promote rectangular comparison to stabilized Cuntz comparison, then deduce diagonalization for $a^2,b^2,ab$ without adding nuclearity or simplicity. The proof must account for zero positive elements as well.

## Sources

- OpenAI, [ExactInfiniteness comparator, exact_weaklyPurelyInfinite_stronglyPurelyInfinite](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ExactInfiniteness.lean#L170-L174).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/303.md).
