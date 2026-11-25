# Subsequence criterion for convergence in probability

Let $\mu$ be a finite measure on a measurable space $\Omega$ (in probability, a probability measure), let $X_n : \Omega \to \mathbb{R}$ ($n \in \mathbb{N}$) be $\mu$-almost everywhere strongly measurable, and let $Y : \Omega \to \mathbb{R}$ be any function. Then $X_n \to Y$ in measure, that is $\mu(\{\omega : |X_n(\omega) - Y(\omega)| > \varepsilon\}) \to 0$ for every $\varepsilon > 0$, if and only if every subsequence $(X_{n_k})$ has a further subsequence $(X_{n_{k_j}})$ with $X_{n_{k_j}}(\omega) \to Y(\omega)$ for $\mu$-almost every $\omega$.

## Idea

Convergence in probability is weaker than almost sure convergence: indicators of intervals that sweep across $[0, 1]$ again and again, ever shorter, tend to $0$ in probability under Lebesgue measure but converge at no point. The criterion says how much almost sure convergence remains. If $X_n \to Y$ in measure, pick $n_{k_j}$ with $\mu(|X_{n_{k_j}} - Y| > 2^{-j}) < 2^{-j}$; the Borel–Cantelli lemma gives almost everywhere convergence. Conversely, if convergence in measure fails, some subsequence has $\mu(|X_{n_k} - Y| > \varepsilon) \ge \delta$ for fixed $\varepsilon, \delta > 0$; since on a finite measure almost everywhere convergence implies convergence in measure, no further subsequence converges almost everywhere. The criterion turns limit theorems for almost sure convergence, such as dominated convergence, into ones for convergence in probability.

## Statements

- [Convergence in probability via subsequential a.s. convergence](convergence-in-probability-iff-subsequen.md)
- [Convergence in measure in the textbook ε-formulation](tendsto-in-measure-iff-tendsto-measure-a.md): textbook ε-formulation of convergence in measure, used in the proof
