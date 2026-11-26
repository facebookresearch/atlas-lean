# Gowers uniformity norms

The Gowers norms $\|f\|_{U^d}$ of a function on a finite abelian group measure how far $f$ is from being random with respect to the structures of "degree $d - 1$": $\|f\|_{U^d}^{2^d}$ is the average of $f$ over $d$-dimensional cubes $(x + \omega \cdot h)_{\omega \in \{0,1\}^d}$, with complex conjugates on the odd vertices. Gowers introduced them in his proof of Szemerédi's theorem (2001), as the right notion of pseudorandomness for counting progressions of length $k = d + 1$: by the generalized von Neumann theorem, $k$-term progressions are controlled by $U^{k-1}$. For $d = 2$ they reduce to Fourier analysis, $\|f\|_{U^2} = \|\hat f\|_{\ell^4}$, and a large $U^2$ norm means correlation with a character; for $d \ge 3$ an inverse theorem must use polynomial phases, which is the subject of higher-order Fourier analysis.

The definition follows Green and Tao's recursion $\|f\|_{U^{d+1}}^{2^{d+1}} = \mathbb{E}_h \|\Delta_h f\|_{U^d}^{2^d}$ and is equal to the cube average. Averages are normalised expectations; Gowers's original sums differ by powers of $|G|$.

## Definitions and the cube formula

- [Multiplicative derivative](mul-deriv.md)
- [Gowers uniformity norm, raised to the power $2^d$](gowers-pow.md)
- [Gowers uniformity norm](gowers-norm.md)
- [Gowers norms as cube averages](gowers-pow-eq-cube-average.md)
- [Gowers inner product](gowers-inner.md)

## Positivity, monotonicity, Cauchy–Schwarz and the triangle inequality

- [Cauchy–Schwarz step for Gowers powers](sq-norm-gowers-pow-le-and-real.md)
- [Gowers powers are nonnegative](gowers-pow-succ-re-nonneg.md)
- [Monotonicity of the Gowers norms](gowers-norm-le-gowers-norm-succ.md)
- [Gowers–Cauchy–Schwarz inequality](norm-gowers-inner-le.md)
- [Triangle inequality for the Gowers norms](gowers-norm-add-le.md)
- [Gowers norms dominate the mean](norm-expect-le-gowers-norm.md)

## The norms $U^1$ and $U^2$ and Fourier analysis

- [The $U^1$ power is the squared modulus of the mean](gowers-pow-one.md)
- [The $U^1$ norm is the modulus of the mean](gowers-norm-one.md)
- [The $U^2$ power as an average over two-dimensional cubes](gowers-pow-two.md)
- [Gowers $U^2$ inner product](gowers-inner-two.md)
- [Fourier expansion of the Gowers $U^2$ inner product](card-pow-four-mul-gowers-inner-two.md)
- [Fourth moment of the Fourier transform](card-pow-four-mul-gowers-pow-two.md)
- [The $U^2$ norm is the $\ell^4$ norm of the Fourier transform](gowers-norm-two-eq.md)
- [Inverse theorem for the $U^2$ norm](exists-character-correlation-of-le-gower.md)

## Counting arithmetic progressions

- [Three-term progression count](ap-count-three.md)
- [Fourier expansion of the three-term progression count](card-pow-three-mul-ap-count-three.md)
- [Generalized von Neumann theorem for three-term progressions](norm-ap-count-three-le-gowers-norm-two.md)
- [Generalized von Neumann theorem, general form](norm-expect-prod-le-gowers-norm.md)
- [Generalized von Neumann theorem](norm-ap-count-le-gowers-norm.md)

## Inverse theorems and bounds

- [Inverse theorem for the $U^3$ norm over $\mathbb{F}_5^n$](u3-inverse-f5.md)
- [Gowers's bound for Szemerédi's theorem](szemeredi-gowers-bound.md)

## Related topics

- [Fourier transform on finite abelian groups](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-transform-on-finite-abelian-groups/README.md): the transform, inversion and Plancherel formula behind $\|f\|_{U^2} = \|\hat f\|_{\ell^4}$.
- [Fourier transform on finite groups](../../../../RepresentationTheory/finite-group-representations/fourier-transform-on-finite-groups/README.md): the non-abelian Fourier transform, of which the abelian one is the case where every irreducible representation is a character.
- [Freiman and Balog–Szemerédi–Gowers theorems](../../sumsets-inverse-theorems/freiman-and-balog-szemer-di-gowers-theorems/README.md): the inverse theorems of additive combinatorics used to prove inverse theorems for $U^3$ and $U^k$.
- [Szemerédi's theorem](../szemeredi.md): the qualitative statement whose quantitative form motivated the norms.
- [Number of arithmetic progressions in dense sets](../number-of-arithmetic-progressions-in-dense-sets/README.md): counts of progressions, which the generalized von Neumann theorem compares with those of random sets.
- [Graph limits](../../../../GraphTheory/random-graphs/graph-limits/README.md): homomorphism densities and the counting lemma, the graph analogues of cube densities and of the generalized von Neumann theorem; $\|1_A\|_{U^2}^4$ is the four-cycle density of the sum graph $1_A(x + y)$.
- [Sidorenko's conjecture](../../../../GraphTheory/extremal-graph-theory/sidorenko-s-conjecture/README.md): its four-cycle case for the sum graph of $A$ is the bound $\|1_A\|_{U^2} \ge \delta$.
- [Triangle density and flag algebras](../../../../GraphTheory/extremal-graph-theory/triangle-density-and-flag-algebras/README.md): Razborov's flag algebras prove density inequalities by combining averaging identities with Cauchy–Schwarz, as the Gowers–Cauchy–Schwarz inequality does for cube densities.
