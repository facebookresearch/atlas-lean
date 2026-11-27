# Fourier formula for noise stability

For every $f : \{-1, 1\}^n \to \mathbb{R}$ and every real $\rho$,

$$\mathrm{Stab}_\rho[f] = \sum_{S \subseteq \{0, \dots, n-1\}} \rho^{|S|}\, \hat f(S)^2
= \sum_{k=0}^{n} \rho^k\, \mathbf{W}^k[f],$$

where $\mathbf{W}^k[f] = \sum_{|S| = k} \hat f(S)^2$ is the Fourier weight of $f$ at degree $k$.
Noise stability is thus a generating function for the Fourier weights; its derivative at
$\rho = 1$ is the total influence.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 2.49.
