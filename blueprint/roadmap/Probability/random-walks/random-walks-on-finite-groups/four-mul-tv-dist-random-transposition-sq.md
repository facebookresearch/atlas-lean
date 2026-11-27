# Upper bound for random transpositions

Let $n \ge 1$ and let $V_i$ ($i \in \iota$) be a complete set of irreducible complex representations of $S_n$, with
dimensions $d_i$ and characters $\chi_i$, and let $\tau$ be a transposition. For every $k$, the law
$T^{*k}$ of $k$ [random transpositions](random-transposition.md) satisfies

$$4\,\|T^{*k} - U\|_{TV}^2 \le \sum_{i \,:\, V_i \text{ non-trivial}} d_i^2 \operatorname{Re}\Bigl(\frac1n + \frac{n-1}{n}\,\frac{\chi_i(\tau)}{d_i}\Bigr)^{2k}.$$

(The characters of $S_n$ are integers, so the real part is the number itself.)

This is Lemma 14, equation (3.1), of Diaconis and Shahshahani, stated there for the $\ell^1$
norm $\|\cdot\| = 2\,\|\cdot\|_{TV}$ (hence the factor $4$ here). The proof is theirs: the
[upper bound lemma](upper-bound-lemma.md) applied to $T^{*k}$; by
[the Fourier transform of the random-transposition measure](fourier-random-transposition.md), each
transform $\widehat{T^{*k}}(V_i)$ is the scalar $c_i^k$ with
$c_i = \tfrac1n + \tfrac{n-1}{n}\,\chi_i(\tau)/d_i$, and $T$ is invariant under inversion, so the
term of $V_i$ is $d_i \cdot d_i c_i^{2k}$. Section 3 of Diaconis and Shahshahani starts from this
inequality and bounds the sum, using Frobenius's formula for $\chi_i(\tau)/d_i$, the dimension
bound $d_\lambda \le \binom{n}{\lambda_1}\sqrt{(n-\lambda_1)!}$ and monotonicity under the dominance
order, to reach the [$\tfrac12 n \log n$ upper bound](diaconis-shahshahani-upper.md).

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Lemma 14 and equation (3.1); Corollary 1.
- P. Diaconis, *Applications of non-commutative Fourier analysis to probability problems*,
  Saint-Flour lecture notes, Lecture Notes in Math. 1362 (1988), Lemma 4.2.
