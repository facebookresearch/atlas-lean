# Non-pretentious multiplicative functions do not correlate with polynomial phases on short intervals on average

**Non-pretentious multiplicative functions do not correlate with polynomial phases on short
intervals on average.** For a function $g$ on the integers, a natural number $k$, a real $x$ and a
real $H > 0$ write

$$
\|g\|_{u^{k+1}[x, x+H]} = \sup_{\deg P \le k} \frac{1}{H}
\Bigl| \sum_{\lceil x \rceil \le n \le \lfloor x + H \rfloor} g(n) e^{-2\pi i P(n)} \Bigr|,
$$

the supremum taken over real polynomials $P$ of degree at most $k$. For functions
$f, g \colon \mathbb{N} \to \mathbb{C}$ and a real $X$ let

$$
\mathbb{D}(f, g; X) =
\Bigl( \sum_{p \le X} \frac{1 - \operatorname{Re}\bigl(f(p) \overline{g(p)}\bigr)}{p} \Bigr)^{1/2},
$$

the sum taken over primes $p \le X$, and for a positive integer $Q$ let $M(f; X, Q)$ be the
infimum of $\mathbb{D}(f, n \mapsto \chi(n) n^{it}; X)$ over real $t$ with $|t| \le X$, positive
integers $q \le Q$ and Dirichlet characters $\chi$ modulo $q$.

Let $k$ be a natural number, $\theta$ a real number with $0 < \theta < 1/2$ and $\eta > 0$ a real
number. Then there are a positive integer $Q$ and real numbers $C > 0$ and $B$ such that the
following holds for every multiplicative arithmetic function $f \colon \mathbb{N} \to \mathbb{C}$
with $|f(n)| \le 1$ for all $n$, extended to the integers by $f(n) = 0$ for $n \le 0$, every real
$X \ge 1$ and every real $H$ with $X^\theta \le H \le X^{1-\theta}$: if

$$
\int_X^{2X} \|f\|_{u^{k+1}[x, x+H]} \, dx \ge \eta X,
$$

then $M(f; C X^{k+1} / H^{k+1}, Q) \le B$.

## Sources

- K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, and T. Ziegler, `Higher uniformity of bounded multiplicative functions in short intervals on average`, Annals of Math, 197 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-2-BoundedMultiplicativeFunctions.lean Via leanprover/lean-eval@38361be, problem `annals_bounded_multiplicative_functions`.
