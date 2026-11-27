# Low-degree functions are anticoncentrated

Let $f : \{-1,1\}^n \to \mathbb{R}$ have degree at most $k$, mean $\mu$ and variance $\sigma^2 > 0$. Then for $0 \le t \le 1$,

$$\Pr_x\big[|f(x) - \mu| > t\sigma\big] \ge \frac{(1 - t^2)^2}{9^k},$$

and in particular $\Pr[|f - \mu| > \sigma/2] \ge \frac{9}{16}\, 9^{-k}$. So a nonconstant low-degree polynomial is not concentrated near its mean on more than a $1 - 9^{-O(k)}$ fraction of the cube.

## Proof sketch

Apply the Paley–Zygmund inequality with $\theta = t^2$ to $Z = (f - \mu)^2$, which has $\mathbb{E}[Z] = \sigma^2$ and $\mathbb{E}[Z^2] \le 9^k\sigma^4$ by the Bonami Lemma applied to $f - \mu$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md)
- [The Paley–Zygmund inequality](../../../Probability/concentration-inequalities/paley-zygmund.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
