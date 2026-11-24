# Statement of the Korolev–Shevtsova structural Berry–Esseen bound

For a probability
measure $\mu$ on $\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. This is the
proposition that for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$
and finite third absolute moment and every integer $n \ge 1$,

$$\Delta_n(\mu) \le \frac{0.34445\,(\beta_3(\mu) + 0.489)}{\sqrt{n}}.$$

## Sources

- catalogue C19a, KS2009 upper-row comment, and the exact retained Shevtsova2011 quotation at lines 141-148. The additive offset is 0.489, not 0.429.
