# Vanishing of the Crouzeix evaluation terms on a zero Hilbert space

For an operator $A$ on the zero complex Hilbert space, the unit-vector numerical range $W=\{\langle x,Ax\rangle:\|x\|=1\}$ is empty (the inner product is linear in its second argument), and for every coefficient size and every matrix function the supremum norm over $W$ is set to zero. For each $m>0$ the completed Hilbert tensor product $H\widehat\otimes\mathbb C^m$ has only the zero bounded endomorphism. In particular all matrix polynomial evaluations, matrix holomorphic evaluations using an epsilon-selected contour, and rational evaluations are zero and each has norm at most twice the corresponding supremum norm on $W$. In the polynomial case the evaluation is the sum of the completed $A^k\otimes B_k$. In the holomorphic case the selected $C^1$ contour is closed in $U\setminus\overline W$, with prescribed winding one on $\overline W$ and zero outside $U$, and the scalar entry evaluations are Dunford integrals. In the rational case they are numerator evaluations times the totalized inverse of the denominator evaluations. No contour-existence, holomorphy or pole-avoidance hypothesis is required in this zero-space clause.

## Depends on

- Hilbert tensor completion and the selected holomorphic and totalized rational evaluation definitions.

## Proof depends on

- Subsingleton of the completed amplification when one tensor factor is zero.

## Expansion

Establish the zero amplification without requiring the contour predicate to be inhabited. Move all evaluations into the same zero operator space and prove the no-unit-vector clause separately.

## Sources

- OpenAI, [HilbertCrouzeix comparator, zeroConclusion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HilbertCrouzeix.lean#L136-L138).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/325.md).
