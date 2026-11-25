# Noise stability

For a real number $\rho$ and a function $f : \{-1, 1\}^n \to \mathbb{R}$,
the noise stability of $f$ at $\rho$ is
$\mathrm{Stab}_\rho[f] = \sum_{S \subseteq \{1, \dots, n\}} \rho^{|S|} \hat f(S)^2$, where
$\hat f(S)$ is the Fourier coefficient of $f$ at $S$.

For $-1 \le \rho \le 1$ this is the Fourier expansion of $\mathbb{E}[f(x) f(y)]$ for uniform $x$
and a $\rho$-correlated copy $y$ of $x$.

It [agrees](noise-stability-eq-bool-noise-stab.md) with the correlation definition
$\mathbb{E}[f \cdot T_\rho f]$ of
[noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md).
