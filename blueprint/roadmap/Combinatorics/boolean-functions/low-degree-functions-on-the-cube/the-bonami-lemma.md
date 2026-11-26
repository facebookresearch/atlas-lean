# The Bonami Lemma

If $f : \{-1,1\}^n \to \mathbb{R}$ has degree at most $k$, then

$$\mathbb{E}[f^4] \le 9^k \big(\mathbb{E}[f^2]\big)^2, \qquad\text{equivalently}\qquad \|f\|_4 \le \sqrt{3}^{\,k}\, \|f\|_2,$$

and more generally $\|f\|_q \le \sqrt{q - 1}^{\,k} \|f\|_2$ for every $q \ge 2$. Low-degree functions of uniform random bits are therefore "reasonable" random variables.

## Proof sketch

Induct on $n$: write $f = x_n D + E$ with $\deg D \le k - 1$, $\deg E \le k$, independent of $x_n$. Expanding $\mathbb{E}[(x_nD + E)^4]$, odd powers of $x_n$ vanish, and $\mathbb{E}[D^4] + 6\mathbb{E}[D^2E^2] + \mathbb{E}[E^4]$ is bounded by Cauchy–Schwarz and induction by $9^k(\mathbb{E}[D^2] + \mathbb{E}[E^2])^2$. The general $q$ version follows from hypercontractivity of the noise operator.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Bonami–Beckner hypercontractive inequality](../kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-hypercontractivity-general.md)

## Sources

- A. Bonami, "Étude des coefficients de Fourier des fonctions de L^p(G)", Annales de l'Institut Fourier 20(2), 1970.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
