# Uncertainty principle on the Boolean cube

For every nonzero real function $f$ on $\{-1,1\}^n$,

$$\Pr_x[f(x) \ne 0] \cdot \big|\{S : \hat f(S) \ne 0\}\big| \ge 1,$$

equivalently $|\mathrm{supp}(f)| \cdot |\mathrm{supp}(\hat f)| \ge 2^n$.

## Proof sketch

Combine the two endpoint inequalities: $\|f\|_\infty \le \sum_S|\hat f(S)| \le |\mathrm{supp}\hat f| \max_S|\hat f(S)| \le |\mathrm{supp}\hat f|\, \mathbb{E}|f| \le |\mathrm{supp}\hat f| \Pr[f \ne 0]\,\|f\|_\infty$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Fourier coefficients bounded by the L¹ norm and values by the spectral norm](fourier-coefficients-bounded-by-l1-norm.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
