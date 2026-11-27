# Fourier analysis on the Boolean cube

- [Boolean cube](bool-cube.md)
- [Sign of a Boolean coordinate](cube-val.md)
- [Fourier character on the Boolean cube](cube-chi.md)
- [Fourier coefficient on the Boolean cube](bool-fourier-coeff.md)
- [Fourier degree at most $d$](multilinear-degree-le.md)
- [Sign of true](cube-val-true.md)
- [Sign of false](cube-val-false.md)
- [Coordinate signs square to one](cube-val-mul-self.md)
- [The empty Fourier character is constant one](cube-chi-empty.md)
- [Singleton Fourier characters are coordinate signs](cube-chi-singleton.md)
- [Fourier characters square to one](cube-chi-mul-self.md)
- [The empty Fourier coefficient is the mean](bool-fourier-coeff-empty.md)
- [Fourier coefficients of the zero function](bool-fourier-coeff-zero.md)
- [A character's own Fourier coefficient](bool-fourier-coeff-cube-chi-self.md)
- [Empty Fourier coefficient of a constant function](bool-fourier-coeff-const-empty.md)
- [The zero function satisfies every Fourier degree bound](multilinear-degree-le-zero.md)
- [Fourier degree bounds are monotone](mono.md)
- [Fourier degree is at most the dimension](multilinear-degree-le-of-dimension-le.md)
- [Lagrange basis polynomial of a cube point](cube-basis.md)
- [Multilinear extension](multilinear-extension.md)
- [Lagrange basis polynomials on the cube are point indicators](eval-cube-basis.md)
- [The multilinear extension agrees with its function on the cube](eval-multilinear-extension.md)
- [Multilinear extension of a constant function](multilinear-extension-const.md)
- [Multilinear extension of a coordinate projection](multilinear-extension-projection.md)
- [Boolean degree](boolean-degree.md)
- [Constant functions have Boolean degree zero](boolean-degree-const.md)
- [Coordinate projections have Boolean degree one](boolean-degree-projection.md)
- [All-true function](all-true-function.md)
- [Multilinear extension of the AND function](multilinear-extension-all-true.md)
- [The two-bit AND has Boolean degree two](boolean-degree-all-true-two.md)
- [Fourier degree is at most Boolean degree](multilinear-degree-le-indicator.md)

## Fourier analysis on the subsets of a finite set

- [Fourier character on finite sets](fourier-char.md)
- [Fourier coefficient on the subsets of a finite set](fourier-coeff.md)
- [Number of points of the Boolean cube](card-bool-cube.md)
- [Subsets of a finite set as indicator functions](powerset-equiv-indicator.md)
- [Subsets of a finite set as points of the Boolean cube](powerset-equiv-bool-cube.md)
- [Coordinates of an encoded subset](powerset-equiv-bool-cube-apply.md)
- [Reindexing a subset as a set of coordinates](reindex-finset.md)
- [Decoding a cube point as a subset](decode-bool-cube.md)
- [Decoding inverts encoding](decode-encode.md)
- [Subset characters agree with cube characters](fourier-char-eq-cube-chi.md)
- [Subset Fourier coefficients agree with cube Fourier coefficients](fourier-coeff-eq-bool-fourier-coeff.md)

## Inversion, Plancherel and convolution

- [Fourier inversion on the subsets of a finite set](fourier-inversion.md)
- [Plancherel identity on the subsets of a finite set](fourier-plancherel.md)
- [Convolution on the Boolean cube](bool-conv.md)
- [Convolution is commutative](bool-conv-comm.md)
- [Convolution theorem on the Boolean cube](bool-fourier-coeff-bool-conv.md)
- [Characters are multiplicative](cube-chi-cube-mul.md)
- [Product on the Boolean cube](cube-mul.md)
- [The cube product is commutative](cube-mul-comm.md)
- [Every point is its own inverse](cube-mul-cube-mul-self.md)
- [Signs multiply under the cube product](cube-val-beq.md)
- [Translation-invariance of averages](expect-comp-cube-mul.md)

## Related topics

- [Influences and the noise operator on the Boolean cube](../influences-and-the-noise-operator-on-the-boolean/README.md): influences, total influence, the Poincaré inequality and noise stability, all computed from this Fourier expansion.
- [Blum–Luby–Rubinfeld linearity test](../../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/README.md): the first application of the convolution theorem: testing whether a function is a character.
- [Goldreich–Levin theorem](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/goldreich-levin-theorem/README.md): the hardcore-bit theorem; its proof is an algorithm that finds the large Fourier coefficients of a function given query access.
- [Fourier transform on finite abelian groups](../fourier-transform-on-finite-abelian-groups/README.md): the cube is the group $\mathbb{F}_2^n$, and this expansion is its Fourier transform.
- [Haar system](../../wavelets/haar-system/README.md): identifying $\mathbb{F}_2^m$ with the dyadic intervals of length $2^{-m}$ in $[0,1)$, the characters become Walsh functions, and the first $m$ levels of the Haar basis are another orthonormal basis of the same step functions, localized in space rather than in frequency.
