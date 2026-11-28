# A zero-free half-plane for Dirichlet L-functions

For every positive integer modulus $q$ and every complex Dirichlet character $\chi$ modulo $q$,
let $L(s,\chi)$ denote the continued function given by $\sum_{n\ge1}\chi(n)n^{-s}$ for
$\operatorname{Re}s>1$. Then $L(s,\chi)\ne0$ for each complex $s$ with $\operatorname{Re}s>7/8$,
except that the pair consisting of the principal character and $s=1$ is excluded.
In particular, nonprincipal characters are allowed at $s=1$ and imprimitive characters are included.

The stronger half-plane form of the generalized Riemann hypothesis implies this result; it is not an assumption of the $7/8$ statement.

## Depends on

- [Dirichlet character of a given modulus](../conductors-and-primitive-dirichlet-characters/is-dirichlet-character-modulus.md)

## Proof depends on

- [Zero-free half-planes from Chebyshev window bounds](zero-free-half-planes-from-chebyshev-bounds-on-windows.md)
- [Window bounds for cyclic families of characters](../../../distribution-of-primes/primes-in-progressions/chebyshev-window-bounds-for-cyclic-character-families.md)

## Proof outline

One route is to specialize the cyclic-character window bound to exponent $7/8$, use the one-sided window criterion for each primitive inducing character, then recover the imprimitive characters by the finite Euler-factor identity. Each deleted Euler factor is nonzero in $\operatorname{Re}s>0$. This is a route using the linked results, not a claim that the cited $7/8$ proof uses those particular window bounds: that proof instead uses a certified-band moment detector. Neither route changes the pole exclusion.

## Sources

- [DirichletSevenEighths.lean — `LFunction_ne_zero_of_seven_eighths_lt_re`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirichletSevenEighths.lean#L8-L13)
- [Source proof via certified bands](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean#L15-L44)
