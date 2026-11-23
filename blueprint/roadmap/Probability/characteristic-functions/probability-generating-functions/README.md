# Probability generating function

For a measure $\mu$ on $\Omega$ and a function $X : \Omega \to \mathbb{N}$, the probability generating function of $X$ under $\mu$ is the function $G_X : \mathbb{R} \to \mathbb{R}$ given by $G_X(s) = \int_\Omega s^{X(\omega)} \, d\mu(\omega)$, with $0^0 = 1$ and with the integral taken to be $0$ where $s^X$ is not integrable. When $\mu$ is a probability measure, $G_X(s)$ is the expectation $\mathbb{E}[s^X]$. When $\mu$ is finite and $X$ is measurable, the integral converges for every $|s| \le 1$.

## Idea

The generating function stores the law of a variable with values in $\mathbb{N}$ as the coefficients of a power series: for a finite measure, measurable $X$ and $|s| \le 1$,

$$G_X(s) = \sum_{k=0}^{\infty} s^k \, \mu(\{X = k\}).$$

So $G_X(0)$ is the mass of $\{X = 0\}$, and $G_X(1) = 1$ under a probability measure. Its main use is that independence turns sums into products: $G_{X+Y} = G_X \, G_Y$ on $[-1, 1]$ for independent $X$ and $Y$. For instance a Bernoulli variable with parameter $p$ has $G(s) = 1 - p + ps$, so a sum of $n$ independent copies, a binomial variable, has $G(s) = (1 - p + ps)^n$. The same multiplicativity drives the analysis of branching processes and random sums.

## Statements

- [Probability generating function](pgf.md)
- [Series form of the probability generating function](pgf-eq-tsum.md): power-series form
- [The generating function at $s = 0$](pgf-zero.md): basic property: value at $s = 0$
- [The generating function at $s = 1$](pgf-one.md): basic property: value at $s = 1$
- [Integrability of $s^X$ for $|s| \le 1$](integrable-pow-of-abs-le-one.md): lemma: the defining integral exists for $|s| \le 1$
- [Generating function of a sum of independent variables](pgf-add-of-indep-fun.md): basic property: sums of independent variables
