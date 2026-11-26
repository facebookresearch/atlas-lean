# Second moment method

Let $X$ be a square-integrable real random variable on a probability space with $\mathbb E X \neq 0$. Then

$$\Pr[X = 0] \le \frac{\operatorname{Var} X}{(\mathbb E X)^2} .$$

On the event $X = 0$ one has $|X - \mathbb E X| = |\mathbb E X|$, so this is Chebyshev's inequality at distance $|\mathbb E X|$. Consequently, if $\operatorname{Var} X = o((\mathbb E X)^2)$ along a sequence, then $X \neq 0$ with high probability; for a nonnegative count this means that some counted event occurs.

The source states the lemma for nonnegative $X$; nonnegativity is not needed.

## Background

- [The Paley–Zygmund inequality](../../../Probability/concentration-inequalities/paley-zygmund.md): another second-moment lower bound on $\Pr[X > 0]$; its case $\theta = 0$ is the [Cauchy–Schwarz form](sq-integral-le-integral-sq-mul-measure-r.md).

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Proposition 4.2 (Chebyshev) and Lemma 4.8.
