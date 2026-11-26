# Sinha: (1+eps)-approximate matching relaxations need binom(n, alpha/eps) inequalities

There is an absolute constant $\alpha \in (0,1)$ such that for every even $n$ and every $\varepsilon$ with $\tfrac2n \le \varepsilon \le 1$, every linear extension of every $(1+\varepsilon)$-approximate relaxation of $P_{\mathrm{M}}(n)$ has at least

$$
\binom{n}{\alpha/\varepsilon}
$$

inequalities. This is tight up to the constant $\alpha$: the truncated odd-set relaxation $K_\varepsilon$ uses $n^{O(1/\varepsilon)}$ inequalities.

## Proof sketch

Restrict the nested slack matrix to odd cuts of size about $1/\varepsilon$ and matchings, and relate its nonnegative rank to that of a lopsided version of the unique disjointness matrix, in which one party holds a small set of size $\Theta(1/\varepsilon)$. A hyperplane separation argument with a lopsided corruption bound shows every rectangle carries weight at most $\binom{n}{\alpha/\varepsilon}^{-1}$ relative to the total, which lower-bounds the nonnegative rank and hence the extension complexity.

## Depends on

- [Multiplicatively approximate relaxations of the matching polytope](approximate-polytope-relaxation.md)
- [Dropping large odd-set constraints gives a (1+eps)-approximate matching relaxation](truncated-odd-set-relaxation.md)
- [Braun-Pokutta and Rothvoss: approximate matching relaxations need 2^Omega(min(n, 1/eps)) size](braun-pokutta-no-fprs.md)
- [Fiorini's hyperplane separation lower bound on nonnegative rank](hyperplane-separation-bound.md)

## Proof depends on

- [Dropping large odd-set constraints gives a (1+eps)-approximate matching relaxation](truncated-odd-set-relaxation.md)
- [Fiorini's hyperplane separation lower bound on nonnegative rank](hyperplane-separation-bound.md)

## Sources

- Makrand Sinha, "Lower Bounds for Approximating the Matching Polytope", SODA (2018), ECCC TR17-185.
- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369.
