# Tight lower bounds for deterministic list labeling

For $m = Cn$ with a constant $C > 1$ and universe size larger than $m$, every deterministic online list-labeling algorithm has amortized relabeling cost $\Omega(\log^2 n)$ on some insertion sequence; for $m = n$, every deterministic algorithm has amortized cost $\Omega(\log^3 n)$. Both bounds match the classical upper bounds up to constant factors, and they extend to the class of *smooth* randomized algorithms.

## Proof sketch

Bulánek, Koucký and Saks construct an adversary that repeatedly inserts into the densest region of the current array and analyze a *file-maintenance game* through a recursive potential: at each of $\Theta(\log n)$ scales the adversary forces the algorithm either to spread out a dense region, paying moves linear in its size, or to let density rise at the next scale, and a careful bookkeeping of the prefix densities shows that the algorithm pays $\Omega(\log n)$ per insertion at each of $\Omega(\log n)$ scales.

## Depends on

- [Classical $O(\log^2 n)$ list labeling](list-labeling-log-squared-upper.md)

## Proof depends on

- [Classical $O(\log^2 n)$ list labeling](list-labeling-log-squared-upper.md)

## Sources

- Jan Bulánek, Michal Koucký, Michael Saks, "Tight Lower Bounds for the Online Labeling Problem", STOC (2012); SIAM Journal on Computing 44(6) (2015), arXiv:1112.5636.
