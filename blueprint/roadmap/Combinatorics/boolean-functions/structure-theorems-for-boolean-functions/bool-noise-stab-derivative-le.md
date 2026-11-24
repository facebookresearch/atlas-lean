# Noise stability of a coordinate Laplacian

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ and let $L_i f(x) = (f(x) - f(x^{\oplus i}))/2$ be its
$i$-th coordinate Laplacian. Then

$$\mathrm{Stab}_{1/3}[L_i f] = \sum_{S \ni i} 3^{-|S|}\, \hat f(S)^2 \le \tfrac13\, \mathrm{Inf}_i[f]^{3/2}.$$

Since $\mathrm{Stab}_{1/3}[L_i f] = \tfrac13\, \mathrm{Inf}^{(1/3)}_i[f]$, this is Corollary 9.12
restated for $L_i f$ instead of $D_i f$. It is the form in which the proof of Theorem 9.28 uses
the corollary.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Corollary 9.12 and the proof of Theorem 9.28.
