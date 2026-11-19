# Chow's theorem

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ be a linear threshold function, $f = \mathrm{sgn}(\ell)$ for a
polynomial $\ell$ of degree at most $1$ that never vanishes on the cube, and let
$g : \{-1, 1\}^n \to \{-1, 1\}$ be any Boolean function. If $\hat g(S) = \hat f(S)$ for every
$|S| \le 1$, then $g = f$. A linear threshold function is determined, among all Boolean
functions, by its $n + 1$ Chow parameters $\hat f(\emptyset), \hat f(\{1\}), \dots, \hat f(\{n\})$.

The proof compares $\mathbb{E}[f \ell] = \mathbb{E}[|\ell|]$ with $\mathbb{E}[g \ell]$, which is equal by
Plancherel and at most $\mathbb{E}[|\ell|]$ pointwise, with equality only where $g = f$. Every linear
threshold function admits such an $\ell$ (perturb the constant term), as the source's proof
assumes.

## Sources

- C. K. Chow, "On the characterization of threshold functions", *Proc. 2nd Annual Symposium on
  Switching Circuit Theory and Logical Design (FOCS)* (1961), 34–38.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 5.1.
