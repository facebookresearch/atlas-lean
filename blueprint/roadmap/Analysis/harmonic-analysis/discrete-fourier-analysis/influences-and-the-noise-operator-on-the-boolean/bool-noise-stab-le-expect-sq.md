# Noise stability is at most the second moment

For $-1 \le \rho \le 1$ and every $f : \{-1, 1\}^n \to \mathbb{R}$,
$\mathrm{Stab}_\rho[f] \le \mathbb{E}[f^2]$: each $\rho^{|S|} \le 1$ in the Fourier formula, and
$\sum_S \hat f(S)^2 = \mathbb{E}[f^2]$ by Parseval. For $f : \{-1, 1\}^n \to \{-1, 1\}$ this says
$\mathrm{Stab}_\rho[f] \le 1$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 2.49 and Parseval's Theorem (Section 1.4).
