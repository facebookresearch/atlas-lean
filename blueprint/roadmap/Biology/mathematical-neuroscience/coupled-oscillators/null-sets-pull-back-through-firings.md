# Null sets pull back through firings

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. The groups of a phase configuration $\phi \in [0, 1)^N$ are the classes of oscillators that share a phase; under [firing](fire.md) a group of size $k$ fires with strength $s(k)$. For a partition of the $N$ oscillators into classes and one class $c_0$ of it, its section is the set of configurations whose groups are exactly these classes and whose oscillators in $c_0$ have phase $0$ (the group $c_0$ has just fired), identified with a subset of $(0, 1)^{K-1}$ by the phases of the other groups, $K$ being the number of classes: the state space $S_{K-1}$ of Sections 3.1 and 3.5, up to the order of the groups, measured by $(K-1)$-dimensional Lebesgue measure. Fix a partition into $K \ge 2$ classes with its section $Z$, a partition into $K'$ classes with $2 \le K' < K$ with its section $Z'$, a set $E \subseteq Z'$ of $(K'-1)$-dimensional Lebesgue measure zero, and $r \ge 1$. Then the set of $\phi \in Z$ whose first $r - 1$ firings cause no absorption, whose $r$-th firing causes one, and with $\operatorname{fire}^{[r]}(\phi) \in E$ has $(K-1)$-dimensional Lebesgue measure zero: a null set of states reached by a first merger pulls back to a null set of states of the section before it.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Section 3.5, the sets $B_{r,k}$ in the proof of Theorem 3.2. <https://doi.org/10.1137/0150098>
