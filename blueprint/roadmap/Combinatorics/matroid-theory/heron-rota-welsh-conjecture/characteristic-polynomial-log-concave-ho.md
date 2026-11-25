# Adiprasito–Huh–Katz theorem (Heron–Rota–Welsh conjecture)

For every finite matroid $M$ on a ground set $E$ with rank function $r$, let $w_k(M)$ be the
absolute value of the coefficient of $\lambda^{r(E) - k}$ in the characteristic polynomial
$\chi_M(\lambda) = \sum_{I \subseteq E} (-1)^{|I|} \lambda^{r(E) - r(I)}$ when $k \le r(E)$,
and $w_k(M) = 0$ when $k > r(E)$. Then $w_{k-1}(M) \, w_{k+1}(M) \le w_k(M)^2$ for every
natural number $k \ge 1$.

This is the conjecture of Heron, Rota and Welsh, which extends Read's unimodality conjecture
and Hoggar's log-concavity conjecture for chromatic polynomials of graphs. History of the
proof:

- Huh proved it for matroids representable over a field of characteristic $0$, which includes
  graphs, by identifying the coefficients with mixed multiplicities of a hyperplane
  arrangement (*Milnor numbers of projective hypersurfaces and the chromatic polynomial of
  graphs*, Theorem 3).
- Huh and Katz extended it to matroids realizable over some field, by identifying the
  coefficients of the reduced characteristic polynomial with intersection numbers on a toric
  variety and applying the Khovanskii–Teissier inequality (*Log-concavity of characteristic
  polynomials and the Bergman fan of matroids*, Theorems 1.1 and 6.2).
- Adiprasito, Huh and Katz proved it for all matroids (Theorem 9.9 (2)) by constructing the
  Chow ring of an arbitrary matroid and proving the hard Lefschetz theorem and the
  Hodge–Riemann relations for it (Theorem 1.4).

## Informally uses

- [Log-concavity of the reduced characteristic polynomial](reduced-char-poly-coeff-log-concave.md):
  the proof of Theorem 9.9 (2) deduces it from the log-concavity of the coefficients of
  $\chi_M(\lambda)/(\lambda - 1)$ by convolving with $(1, 1)$.

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Conjecture 1.1 (definition of $\chi_M$ and $w_k$) and
  Theorem 9.9 (2), https://arxiv.org/abs/1511.02888.
- J. Huh, *Milnor numbers of projective hypersurfaces and the chromatic polynomial of graphs*,
  J. Amer. Math. Soc. 25 (2012), 907–927, Theorem 3, https://arxiv.org/abs/1008.4749.
- J. Huh and E. Katz, *Log-concavity of characteristic polynomials and the Bergman fan of
  matroids*, Math. Ann. 354 (2012), 1103–1116, Theorems 1.1 and 6.2,
  https://arxiv.org/abs/1104.2519.
- R. P. Stanley, *Positivity Problems and Conjectures in Algebraic Combinatorics* (1999),
  Problem 25.
