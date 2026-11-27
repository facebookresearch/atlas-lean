# A nonconstant monotone function has a large degree-one coefficient

For every nonconstant monotone $f : \{-1,1\}^n \to \{-1,1\}$ some coordinate $i$ has

$$\hat f(\{i\})^2 \ge \exp\Big(-10\,\frac{\mathbf{I}[f]}{\mathrm{Var}[f]}\Big).$$

## Proof sketch

For monotone $f$, $\hat f(\{i\}) = \mathbf{Inf}_i[f]$; apply the KKL edge-isoperimetric theorem, whose bound $9\tilde{\mathbf{I}}^{-2} 9^{-\tilde{\mathbf{I}}}$ squared dominates $e^{-10\tilde{\mathbf{I}}}$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [KKL edge-isoperimetric theorem](kkl-edge-isoperimetric-theorem.md)
- [A direction is unate exactly when its influence equals the absolute value of its degree-one coefficient](unate-direction-influence-equals-coefficient.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
