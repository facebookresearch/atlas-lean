# Maximally probable at-most-r-furcating topologies are bifurcating

**Setting.** Among labeled topologies of a given class on $n$ leaves, a *maximally probable* one is a topology with the largest number of labeled histories (hence, under models where every labeled history is equally likely, the largest probability). For bifurcating trees without simultaneity, Hammersley and Grimmett showed that the maximizing unlabeled shape is unique and given recursively by $U^*_n = U^*_t \oplus U^*_{n-t}$ with $t = 2^{\lfloor \log_2((n-1)/3) \rfloor + 1}$ for $n \ge 3$.

**Theorem.**
1. For $n \ge 3$, $N(U_n^*)$ increases monotonically in $n$.
2. For every $r \ge 2$ and $n \ge 1$, the maximally probable at-most-$r$-furcating tree topology (without simultaneity) is unique and equals the maximally probable strictly bifurcating topology $U^*_n$.
3. With simultaneous events permitted, for every $r \ge 2$ and $n \ge 1$, an at-most-$r$-furcating shape maximizing the number of tie-permitting labeled histories is strictly bifurcating.

## Depends on

- [Labeled histories of at-most-r-furcating trees](labeled-histories-of-at-most-r-furcating-trees.md)

## Proof idea

By the hook-length formula $N(T) = w(T)!/\prod_v w(v)$, a topology with more internal nodes has a larger factorial numerator. Splitting a multifurcating node into a cascade of binary nodes adds internal nodes and can be arranged so that the gain in $w(T)!$ dominates the new factors in the denominator; together with monotonicity of $N(U^*_n)$ this shows that any multifurcating candidate is beaten by a bifurcating one, and the Hammersley–Grimmett shape is optimal among those. For tie-permitting histories the counts $E(T, z)$ by number $z$ of distinct event times satisfy a recursion over the root split, and the same refinement argument applies.

## Sources

- E. H. Dickey and N. A. Rosenberg, "Labeled histories and maximally probable labeled topologies with multifurcation", Discrete Applied Mathematics 391 (2026), 192–203, <https://doi.org/10.1016/j.dam.2026.04.032>. Numbering as in the preprint arXiv:2511.16799v1, <https://arxiv.org/abs/2511.16799v1>: Theorem 7, Proposition 8, Theorem 9, Proposition 11 and Theorem 13.
