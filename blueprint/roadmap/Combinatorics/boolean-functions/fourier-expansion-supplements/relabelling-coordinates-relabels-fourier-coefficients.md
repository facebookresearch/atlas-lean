# Relabelling coordinates relabels Fourier coefficients

Let $e : \iota \to \kappa$ be a bijection between finite coordinate sets and $g$ a real function on $\{-1,1\}^\kappa$. The function $g \circ e^*$ on $\{-1,1\}^\iota$, $(g \circ e^*)(x) = g\big((x_{e^{-1}(j)})_{j \in \kappa}\big)$, has Fourier coefficients $\widehat{g \circ e^*}(S) = \hat g(e(S))$. In particular, for a permutation $\pi$ of $[n]$ and $f^\pi(x) = f(x_{\pi(1)}, \dots, x_{\pi(n)})$, $\widehat{f^\pi}(S) = \hat f(\pi^{-1}(S))$.

## Proof sketch

The character $\chi_S \circ e^{-*}$ equals $\chi_{e(S)}$, and the uniform measure is invariant under relabelling, so the coefficient integrals agree.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Fourier character on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/cube-chi.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
