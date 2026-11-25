# Tightness of the Moran empirical-measure processes in the space of continuous paths

Let $E$ be a compact metric space, $B$ a bounded jump-type mutation generator, and $\mu^N$ the empirical-measure processes of the [Moran systems of $N$ particles](moran-particle-system-with-feller-mutation-on-a.md), with paths in $D([0, T], \mathcal M_1(E))$. If the initial laws converge, the laws of $(\mu^N)_N$ are C-tight: they are tight in $D([0, T], \mathcal M_1(E))$ and every limit point is supported on continuous paths. The proof combines three facts:

- compactness of $\mathcal M_1(E)$ in the weak topology gives the compact-containment condition;
- the [uniform Aldous bounds](uniform-aldous-bounds-for-moran-empirical-measur.md) for the real processes $\langle f, \mu^N \rangle$, $f$ in a countable convergence-determining family of continuous functions, give tightness of the projections, which extends to the measure-valued processes;
- every jump of $\langle f, \mu^N \rangle$ has size at most $2\|f\|/N$, so limit points are continuous.

The jump bound alone does not give tightness; it gives continuity of limits only together with the tightness bounds.

## Depends on

- [Uniform Aldous bounds for Moran empirical-measure projections](uniform-aldous-bounds-for-moran-empirical-measur.md)
- [Moran particle system with bounded mutation on a compact type space](moran-particle-system-with-feller-mutation-on-a.md)

## Proof depends on

- [Aldous tightness criterion in D([0,T],E) with initial and compact-containment conditions](../../../../Probability/convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md)
- [D([0,T],E) is Polish for Polish E](../../../../Probability/convergence-of-measures/skorokhod-space/d-0-t-e-is-polish-for-polish-e.md)
- [Borel sigma-algebra of D equals the coordinate sigma-algebra; fdd determine laws](../../../../Probability/convergence-of-measures/skorokhod-space/borel-sigma-algebra-of-d-equals-the-coordinate-s.md)
- [Prokhorov's theorem: tight sets of probability measures are relatively compact](../../../../Probability/convergence-of-measures/prokhorov-theorem-on-a-polish-space.md)

## Expansion

A full proof page must still establish the extension from the countable family of projections to the measure-valued processes and the continuity of the limit points.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 3 (tightness in $D_E[0, \infty)$), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>
