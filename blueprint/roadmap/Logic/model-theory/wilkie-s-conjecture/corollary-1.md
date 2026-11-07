# Wilkie's conjecture for the real exponential field

Let $X \subseteq \mathbb{R}^n$ be
definable in $\mathbb{R}_{\exp}$. Then there is a polynomial $f$ in two variables with real
coefficients such that the following holds for all natural numbers $g$ and $H$. Let
$X^{\mathrm{trans}}(g, H)$ be the set of points $x = (x_1, \dots, x_n)$ of the transcendental part
$X^{\mathrm{trans}}$ of $X$ whose coordinates are all algebraic over $\mathbb{Q}$, such that the
field $\mathbb{Q}(x) = \mathbb{Q}(x_1, \dots, x_n)$ satisfies $[\mathbb{Q}(x) : \mathbb{Q}] \le g$
and the height $H(x)$ of $x$, the maximum of the absolute multiplicative Weil heights of
$x_1, \dots, x_n$ (taken to be $0$ when $n = 0$), satisfies $H(x) \le H$. Then
$X^{\mathrm{trans}}(g, H)$ is finite and has at most $f(g, \log H)$ elements, where $\log 0$ is
taken to be $0$.

This is Corollary 1 of the source.

## Sources

- G. Binyamini, D. Novikov, and B. Zak, `Wilkie's conjecture for Pfaffian structures`, Annals of Math, 199 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-2-WilkiesConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_wilkies_conjecture`.
