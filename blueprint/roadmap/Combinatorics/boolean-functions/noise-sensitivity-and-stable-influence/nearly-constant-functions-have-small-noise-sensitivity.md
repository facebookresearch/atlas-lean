# Nearly constant Boolean functions have small noise sensitivity

For $f : \{-1,1\}^n \to \{-1,1\}$ with $\alpha = \min(\Pr[f = 1], \Pr[f = -1])$ and every $0 \le \delta \le 1$, $\mathrm{NS}_\delta[f] \le 2\alpha$ and $\mathrm{NS}_\delta[f] \le \delta\, \mathbf{I}[f]$.

## Proof sketch

$f(x) \ne f(y)$ requires $x$ or $y$ to lie in the minority set, and both are uniformly distributed. The second bound follows from the Fourier formula for noise sensitivity and Bernoulli's inequality $1 - (1 - 2\delta)^{k} \le 2\delta k$, valid since $1 - 2\delta \ge -1$.

## Depends on

- [Noise sensitivity](noise-sensitivity.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)

## Proof depends on

- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
