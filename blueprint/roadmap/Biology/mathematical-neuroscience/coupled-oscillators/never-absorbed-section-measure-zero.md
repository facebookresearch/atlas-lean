# Non-absorbing configurations of a section have measure zero

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. The groups of a phase configuration $\phi \in [0, 1)^N$ are the classes of oscillators that share a phase; under [firing](fire.md) a group of size $k$ fires with strength $s(k)$, so groups merged by an absorption act as single oscillators with their own strengths. Fix a partition of the $N$ oscillators into $K \ge 2$ classes and one class $c_0$ of it, and let $Z$ be the set of configurations whose groups are exactly these classes and whose oscillators in $c_0$ have phase $0$ (the group $c_0$ has just fired). The phases of the other $K - 1$ groups identify $Z$ with the set of points of $(0, 1)^{K-1}$ with pairwise distinct coordinates; measure $Z$ by $(K-1)$-dimensional Lebesgue measure in these coordinates. Then the set of $\phi \in Z$ such that $\operatorname{fire}^{[n]}(\phi)$ has $K$ groups for every $n \ge 1$, that is, no absorption ever occurs, has $(K-1)$-dimensional Lebesgue measure zero. This is a statement about the section $Z$ itself, measured in its own $K - 1$ dimensions: a subset of $Z$ has $N$-dimensional measure zero in any case.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)

## Proof depends on

- [The return map is injective](return-map-injective.md)
- [The return map expands volume](return-map-expands-volume.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Section 3.5, Theorem 3.1 and its proof, on the state space of Section 3.1. <https://doi.org/10.1137/0150098>
