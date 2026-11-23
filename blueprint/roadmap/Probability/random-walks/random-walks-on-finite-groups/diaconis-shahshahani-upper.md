# Random transpositions: $\tfrac12 n \log n + cn$ steps suffice (Diaconis–Shahshahani)

Let $T$ be the [random-transposition measure](random-transposition.md) on $S_n$ and $U$ the uniform
distribution. There is a constant $b > 0$ such that for all $n \ge 10$ and all $k$ with

$$c = \frac{k - \tfrac12 n \log n}{n} > 0,$$

the law $T^{*k}$ of $k$ random transpositions satisfies $\|T^{*k} - U\| \le b\, e^{-2c}$.

Diaconis and Shahshahani measure distance with the $\ell^1$ norm
$\|T^{*k} - U\| = \sum_\pi |T^{*k}(\pi) - 1/n!|$, which is twice the total variation distance;
the statement above writes it as $2\,\|T^{*k} - U\|_{TV}$. The constant is universal: the paper computes
it explicitly (end of Section 3 and Remark 1 of Section 5).

Together with the [lower bound](diaconis-shahshahani-lower.md), completed there by a fixed-point
argument, this shows that random transpositions mix at $\tfrac12 n \log n$, with a window of order
$n$: an instance of the
[cutoff phenomenon](../../markov-chains/mixing-times-of-markov-chains/has-cutoff.md).

The proof starts from the
[upper bound for random transpositions](four-mul-tv-dist-random-transposition-sq.md), a sum over
irreducible representations, and estimates it with Frobenius's character formula, the
dimension bound $d_\lambda \le \binom{n}{\lambda_1}\sqrt{(n-\lambda_1)!}$ (Corollary 2 of the
paper) and a bound on the number of partitions.

## Informally uses

- [Upper bound for random transpositions](four-mul-tv-dist-random-transposition-sq.md): Lemma 14,
  (3.1), of the paper, the inequality the proof of Theorem 1 starts from.
- [Upper bound lemma (Diaconis–Shahshahani)](upper-bound-lemma.md): the proof bounds the distance
  by the sum over non-trivial irreducible representations of $S_n$.
- [Fourier transform of the random-transposition measure](fourier-random-transposition.md): each
  term of that sum is $d_\rho^2\,(1/n + (1 - 1/n)\,\chi_\rho(\tau)/d_\rho)^{2k}$ (Corollary 1 of the
  paper), which the proof then estimates with Frobenius's formula for $\chi_\rho(\tau)/d_\rho$.

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Theorem 1 with (1.1)–(1.4).
