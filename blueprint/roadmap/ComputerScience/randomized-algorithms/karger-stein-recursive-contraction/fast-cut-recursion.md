# The Karger-Stein FastCut recursion

**FastCut** (Karger-Stein) on a weighted multigraph $G$ with $n$ super-vertices: if $n < 7$, contract randomly (edges chosen with probability proportional to weight) down to $2$ super-vertices and return the resulting cut; otherwise let $t = \lceil 1 + n/\sqrt{2}\, \rceil$, independently contract $G$ twice down to $t$ super-vertices, recursively run FastCut on both results, and return the smaller of the two cuts.

## Depends on

- [Edge contraction](../karger-s-algorithm/contract.md)
- [Minimum cut size](../karger-s-algorithm/is-min-cut.md)

## Sources

- D. R. Karger and C. Stein, "A New Approach to the Minimum Cut Problem", Journal of the ACM 43(4), 1996.
