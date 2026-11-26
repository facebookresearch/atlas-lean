# The return map is injective

Let $N \ge 2$, let $f, g : [0, 1] \to [0, 1]$ satisfy the [state-function](state-function.md) hypotheses ($f$ smooth, $f(0) = 0$, $f(1) = 1$, $f' > 0$, $f'' < 0$, inverse $g$), and let the group pulse strengths satisfy $s(k) > 0$ for every group size $k \ge 1$. The groups of a phase configuration $\phi \in [0, 1)^N$ are the classes of oscillators that share a phase; under [firing](fire.md) a group of size $k$ fires with strength $s(k)$, so groups merged by an absorption act as single oscillators with their own strengths. Fix a partition of the $N$ oscillators into $K \ge 2$ classes and one class $c_0$ of it, and let $Z$ be the set of configurations whose groups are exactly these classes and whose oscillators in $c_0$ have phase $0$ (the group $c_0$ has just fired). The phases of the other $K - 1$ groups identify $Z$ with the set of points of $(0, 1)^{K-1}$ with pairwise distinct coordinates. Let $D \subseteq Z$ be the set of $\phi \in Z$ such that each of $\operatorname{fire}^{[1]}(\phi), \dots, \operatorname{fire}^{[K]}(\phi)$ still has $K$ groups, that is, no absorption occurs during the next $K$ firings. Then the return map $R = \operatorname{fire}^{[K]}$ maps $D$ into $Z$ (each group fires once, $c_0$ last), and $R$ is injective on $D$.

## Depends on

- [State Function](state-function.md)
- [Fire](fire.md)

## Sources

- R. E. Mirollo and S. H. Strogatz, Synchronization of pulse-coupled biological oscillators, SIAM J. Appl. Math. 50 (1990), 1645–1662, Sections 3.1–3.2 and 3.5: the return map (3.8) and its injectivity in the proof of Theorem 3.1. <https://doi.org/10.1137/0150098>
