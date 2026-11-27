# Uniform error and regret for selecting the best of finitely many simulated alternatives

Let $X$ be a finite nonempty set, $n \ge 1$, $a < b$ and $\varepsilon > 0$. For each $x \in X$ let $\hat C(x)$ be the average of $n$ independent replications with values in $[a, b]$ and mean $C(x)$; replications for different $x$ may be dependent. Then $P(\max_x |\hat C(x) - C(x)| \ge \varepsilon) \le 2|X| \exp(-2n\varepsilon^2/(b-a)^2)$, and on the complementary event every minimizer $\hat x$ of $\hat C$ satisfies $C(\hat x) - \min_x C(x) < 2\varepsilon$.

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md): the bound for each fixed $x$, followed by a union bound over $X$.

## Background

- [Uniform deviation for a finite class](../../machine-learning/generalization-bounds-and-concentration/finite-class-uniform-deviation.md): the same argument for a finite class of predictors evaluated on one shared sample.

## Sources

- S. Asmussen and P. W. Glynn, *Stochastic Simulation: Algorithms and Analysis*, Springer, 2007
