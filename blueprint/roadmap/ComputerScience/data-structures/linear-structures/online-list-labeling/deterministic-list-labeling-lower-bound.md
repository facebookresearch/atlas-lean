# Tight lower bounds for deterministic list labeling

Consider deterministic online list-labeling algorithms that insert $n$ items, chosen online by an adversary from a universe $\{1, \dots, r\}$, into an array of $m$ slots. For every constant $C > 1$, if $n \le m \le Cn$, $n$ is sufficiently large and $r$ is at least a sufficiently large polynomial in $n$ (for $m \ge 2n$, $r \ge C_1 m$ for an absolute constant $C_1$ suffices), then the adversary forces $\Omega(n \log^2 n)$ moves in total, that is, amortized relabeling cost $\Omega(\log^2 n)$ per insertion. If $n \le m \le n + n^{1-\varepsilon}$ for a constant $\varepsilon \in (0, 1)$ and $r$ is at least a sufficiently large polynomial in $n$, the adversary forces $\Omega(n \log^3 n)$ moves in total, amortized $\Omega(\log^3 n)$ per insertion; this includes the completely packed case $m = n$. Both bounds match the classical upper bounds up to constant factors.

## Proof sketch

Bulánek, Koucký and Saks build on the smooth-algorithm lower bound of Dietz, Seiferas and Zhang. The adversary maintains a chain of $\Theta(\log n)$ nested segments of the array in which most segments keep buffers holding a constant fraction of their parent's items on both sides, while the density degrades by at most a constant factor along the whole chain. It inserts new items into the innermost segment and rebuilds the affected part of the chain whenever the algorithm rearranges the array. As a buffered segment fills up, the items of one of its buffers must move, and charging these moves level by level gives $\Omega(\log n)$ moves per insertion at each of $\Omega(\log n)$ levels; in the nearly packed regime the slack shrinks geometrically and adds one more logarithmic factor.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)
- [Classical $O(\log^2 n)$ list labeling](list-labeling-log-squared-upper.md)

## Sources

- Jan Bulánek, Michal Koucký, Michael Saks, "Tight Lower Bounds for the Online Labeling Problem", STOC (2012); SIAM Journal on Computing 44(6) (2015), arXiv:1112.5636.
