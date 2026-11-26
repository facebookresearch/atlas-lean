# Null sets pull back through firings

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. The groups of a phase configuration $\phi \in [0, 1)^N$ are the classes of oscillators that share a phase. Fix a partition of the $N$ oscillators into $K \ge 2$ classes and one class $c_0$ of it, let $Z$ be the set of configurations whose groups are exactly these classes and whose oscillators in $c_0$ have phase $0$, identified with a subset of $(0, 1)^{K-1}$ by the phases of the other $K - 1$ groups, and let $E \subseteq Z$ have $(K-1)$-dimensional Lebesgue measure zero. Then for every $m \ge 1$ the set of initial configurations $\phi \in [0, 1)^N$ with $\operatorname{fire}^{[m]}(\phi) \in E$ under [firing](fire.md) has Lebesgue measure zero in $[0, 1)^N$. This covers firings with absorptions ($K < N$): a null set of configurations in which groups have merged pulls back to a null set of initial configurations.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Section 3.5, proof of Theorem 3.2. <https://doi.org/10.1137/0150098>
