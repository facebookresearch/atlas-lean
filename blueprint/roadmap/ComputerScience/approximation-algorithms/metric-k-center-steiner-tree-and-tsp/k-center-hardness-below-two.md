# Approximating metric k-center within a factor below 2 is NP-hard

For a graph $G$, the distance $d_G$ with $d_G(u,v) = 1$ for adjacent $u \ne v$, $2$ for nonadjacent $u \ne v$ and $0$ on the diagonal is a metric, and a set $S$ has radius at most $1$ under $d_G$ if and only if $S$ dominates $G$ (otherwise its radius is $2$). Consequently $G$ has a dominating set of size at most $k$ if and only if $r^*_k(d_G) \le 1$, and for every $\alpha < 2$ a polynomial-time $\alpha$-approximation for metric $k$-center would decide the dominating set problem, so none exists unless $\mathrm{P} = \mathrm{NP}$.

## Depends on

- [The k-center objective](k-center-objective.md)
- [Dominating set](../../../GraphTheory/independence-and-domination/dominating-sets/is-dominating.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [DOMINATING SET is NP-complete](../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/dominating-set/dominating-set-np-complete.md)

## Sources

- W.-L. Hsu and G. L. Nemhauser, "Easy and Hard Bottleneck Location Problems", Discrete Applied Mathematics 1(3), 1979.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
