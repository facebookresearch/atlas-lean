# Random transpositions: fewer than $\tfrac12 n \log n$ steps do not suffice (Diaconis–Shahshahani)

Let $T$ be the [random-transposition measure](random-transposition.md) on $S_n$. For every choice
of step numbers $k = k(n)$, with $c = (k - \tfrac12 n \log n)/n$,

$$\|T^{*k} - U\| \ge 2\Bigl(\frac1e - \exp\bigl(-e^{-2c}\bigr)\Bigr) + o(1) \qquad (n \to \infty),$$

in the $\ell^1$ norm $\|\cdot\| = 2\,\|\cdot\|_{TV}$. Precisely: for every $\varepsilon > 0$, eventually
in $n$, $2(e^{-1} - \exp(-e^{-2c})) - \varepsilon \le 2\,\|T^{*k(n)} - U\|_{TV}$. The bound is useful
for $c < 0$.

The proof, which the paper credits to Charles Stein, uses the set $A$ of permutations with a fixed
point: $U(A) \to 1 - 1/e$ (the matching problem), while $T^{*k}(A)$ is at least the probability that
$2k$ balls dropped into $n$ boxes leave a box empty (coupon collecting).

As $c \to -\infty$ this bound tends only to $\|T^{*k} - U\|_{TV} \ge 1/e$. The
[cutoff](../../markov-chains/mixing-times-of-markov-chains/has-cutoff.md) at $\tfrac12 n \log n$ needs
the distance to tend to $1$ before that time, which takes a further argument. At
$k = (1 - \eta) \tfrac12 n \log n$ the number of cards never touched, all of them fixed points, has
mean of order $n^\eta$ and variance at most its mean, so it tends to infinity in probability, while
a uniform permutation has one fixed point on average. Testing for at least $m$ fixed points, with
$m \to \infty$ slowly, then gives total variation distance tending to $1$; with the
[upper bound](diaconis-shahshahani-upper.md), this is the cutoff.

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Theorem 2 and its proof in Section 1.
