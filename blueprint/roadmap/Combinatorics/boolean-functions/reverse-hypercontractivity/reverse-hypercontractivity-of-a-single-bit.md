# Reverse hypercontractivity of a single bit

Let $0 < q \le p \le 1$ with $q < 1$, and $0 \le \rho \le \sqrt{(1-p)/(1-q)}$. For every nonnegative function $f$ of one uniform bit, $\|f\|_p \le \|T_\rho f\|_q$. Equivalently, for $a \ge |b|$ and $\rho^2(1 - q) \le 1 - p$, $\big(\frac{(a+b)^p + (a-b)^p}{2}\big)^{1/p} \le \big(\frac{(a+\rho b)^q + (a - \rho b)^q}{2}\big)^{1/q}$.

## Proof sketch

Normalize $a = 1$ and expand both sides as binomial series in $b$ and $\rho b$; coefficient comparison shows the inequality holds termwise in the stated range of $\rho$.

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
