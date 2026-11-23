# Decay of dilates of an integrable function

Let $f : \mathbb{R} \to \mathbb{R}$ be Lebesgue integrable and let $\lambda > 0$. Then for almost every
$x \in \mathbb{R}$, $n^{-\lambda} f(nx) \to 0$ as $n \to \infty$ through the positive integers.

## Idea

The dilates $x \mapsto f(nx)$ compress the graph of $f$ towards the origin, and the factor
$n^{-\lambda}$ makes them decay almost everywhere. For $\varepsilon > 0$, the substitution
$y = nx$ and Markov's inequality show that the set of $x$ with $|f(nx)| > \varepsilon n^\lambda$ has
measure $\frac1n \, m\{|f| > \varepsilon n^\lambda\} \le \|f\|_1 / (\varepsilon n^{1 + \lambda})$, which
is summable in $n$. By the Borel–Cantelli lemma almost every $x$ lies in only finitely many of these
sets, that is, $|n^{-\lambda} f(nx)| \le \varepsilon$ for all large $n$.

## Statements

- [Decay of dilates of an integrable function](ae-tendsto-rpow-neg-mul-comp-mul-zero.md)
