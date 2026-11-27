# Fourier vanishing for order-six complex Hadamard matrices outside the Tao class

Let $H\in M_6(\mathbb C)$ have entries of modulus one and $H^*H=6I$. The Tao matrix is $(\omega^{E_{ij}})$ with $\omega=e^{2\pi i/3}$ and exponent rows $000000$, $001221$, $010122$, $021012$, $022101$, $012210$. Assume $H$ is not equivalent to this matrix under independent row and column permutations and multiplication of each row and column by a unit complex number. For every permutation of the six coordinates of $(1,1,1,-1,-1,-1)$, giving a charge vector $a$, one has $(1/6)\sum_{k=1}^6\prod_{i=1}^6 H_{ik}^{a_i}=0$. The negative exponents are complex inverses; the entries never vanish.

## Depends on
The full phase-and-permutation equivalence, integer powers on nonzero complex entries, and the exact cubic exponent matrix.

## Proof depends on
- [Cube-fiber cancellation for order-six complex Hadamard matrices](sum-row-ratio-eq-zero-of-two-cube-values.md), for the ratio-fiber cancellation in the case where the entrywise square is Hadamard and the cubes take at most two values.

The argument also needs the character-sum product identities, the entrywise-square Hadamard dichotomy, and the remaining classification of the exceptional class via ratio fibers.

## Expansion
State the two product identities and their permutation transport, then prove the implications for the squared matrix and the cubic equivalence classification. Do not replace equivalence under arbitrary phases by equality to one dephased representative.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MUBSix.lean#L56-L61) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/266.md).
