# Sharp Level-1 inequality for {0,1}-valued functions

For every $A \subseteq \{-1,1\}^n$ of volume $\alpha \in [0, 1]$,

$$\mathbf{W}^1[\mathbf{1}_A] \le 2\alpha^2\ln\frac{1}{\alpha}$$

(both sides $0$ at $\alpha = 0$). The constant $2$ is asymptotically optimal, as shown by Hamming balls (threshold functions $\mathbf{1}\{\sum_i x_i > t\sqrt n\}$ with $n \to \infty$, then $t \to \infty$); subcubes give only $\alpha^2\log_2(1/\alpha)$.

## Proof sketch

Optimize the bound $\mathbf{W}^1 \le (\alpha^{2/(1+\rho)} - \alpha^2)/\rho$ over $\rho \to 0^+$: $\alpha^{2/(1+\rho)} = \alpha^2 \alpha^{-2\rho/(1+\rho)} \le \alpha^2(1 + 2\rho\ln(1/\alpha) + O(\rho^2))$-type estimates, made exact by convexity, give $2\alpha^2\ln(1/\alpha)$.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)

## Proof depends on

- [Low-degree Fourier weight of small sets](low-degree-fourier-weight-of-small-sets.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
