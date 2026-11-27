# Weak two-function hypercontractivity on the cube

For $0 \le r, s \le 1$, $0 \le \rho \le \sqrt{rs}$, and real functions $f, g$ on $\{-1,1\}^n$,

$$\mathbb{E}_{(x,y)\ \rho\text{-correlated}}\big[f(x)\, g(y)\big] = \mathbb{E}[f\, T_\rho g] \le \|f\|_{1+r}\,\|g\|_{1+s}.$$

Consequently $\|T_\rho g\|_2 \le \|g\|_{1+\rho^2}$ and $\mathrm{Stab}_\rho[g] \le \|g\|_{1 + \rho}^2$.

## Proof sketch

Prove the inequality for one bit by an elementary two-point inequality and tensorize over coordinates: the noise operator acts independently on each coordinate, and the two-function form is preserved under products of independent spaces by Hölder's inequality.

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Bonami–Beckner hypercontractive inequality](../kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-hypercontractivity-general.md)
- [L^p seminorms under a probability measure increase with the exponent](../fourier-expansion-supplements/lp-norms-increase-with-p.md)

## Sources

- A. Bonami, "Étude des coefficients de Fourier des fonctions de L^p(G)", Annales de l'Institut Fourier 20(2), 1970.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
