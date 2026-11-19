# Fourier transform of the random-transposition measure

Let $n \ge 1$, and let $\rho$ be an irreducible representation of $S_n$ on a finite-dimensional complex vector space
of dimension $d_\rho$, with character $\chi_\rho$, and let $\tau$ be any transposition. The Fourier
transform of the [random-transposition measure](random-transposition.md) $T$ at $\rho$ is the scalar

$$\hat T(\rho) = \Bigl(\frac1n + \frac{n-1}{n}\,\frac{\chi_\rho(\tau)}{d_\rho}\Bigr) I .$$

$T$ is a class function, so its transform is a scalar by
[Fourier transform of a class function at an irreducible representation](../../../RepresentationTheory/finite-group-representations/fourier-transform-on-finite-groups/fourier-eq-smul-one-of-is-class-function.md);
the scalar follows from $T(\mathrm{id}) = 1/n$, the $\binom n2$ transpositions of mass $2/n^2$ and
the constancy of $\chi_\rho$ on transpositions. With the convolution law
$\widehat{T^{*k}}(\rho) = \hat T(\rho)^k$ this reduces the analysis of $k$ random transpositions to
powers of real numbers (the remark after Corollary 1 of the paper).

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Corollary 1.
