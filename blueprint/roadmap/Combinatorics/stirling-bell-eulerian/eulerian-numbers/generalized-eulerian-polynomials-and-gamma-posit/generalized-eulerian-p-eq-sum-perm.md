# Permutation expansion of the generalized Eulerian polynomials

Let $P_n(q, t; x, y)$ be
the generalized Eulerian polynomial and let $S_n$ be the set of permutations of
$\{0, 1, \dots, n-1\}$. For $w \in S_n$ write $\mathrm{cyc}(w)$ for the number of cycles of $w$
(fixed points counted as cycles), $\mathrm{fix}(w)$ for the number of fixed points of $w$, and
$\mathrm{exc}(w)$ for the number of excedances of $w$, the points $i$ with $w(i) > i$. Then for
all rational numbers $q, t, x, y$ with $x \ne y$ and every $n \ge 0$,

$$
P_n(q, t; x, y) = \sum_{w \in S_n} q^{\mathrm{cyc}(w)} t^{\mathrm{fix}(w)} x^{\mathrm{exc}(w)}
y^{\mathrm{exc}(w^{-1})} (x + y)^{\mathrm{fix}(w)}.
$$

## Sources

- Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 2 (`jis-2024-24.1.5-thm-2`).
