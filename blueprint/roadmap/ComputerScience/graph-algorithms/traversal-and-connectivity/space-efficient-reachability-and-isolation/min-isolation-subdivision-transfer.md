# Min-isolation transfers to unique shortest walks after subdivision

Replace every vertex $v$ of a layered digraph with weight $\mathrm{wt}(v)$ by a chain of $\mathrm{wt}(v) + 1$ vertices. If $\mathrm{wt}$ is min-isolating, then in the subdivided graph every vertex reachable from an original source has a unique shortest walk from it, so the double-counting scan has exactly one passing transcript in every round; conversely, unique transcripts at every original source in a saturated round certify that $\mathrm{wt}$ is min-isolating. Combined with an ordered search over seeds of the logarithmic-space generator, this gives a controller that verifies a seed before using it.

## Depends on

- [Layered digraphs and min-isolating weights](layered-digraphs-and-min-isolation.md)
- [Reinhardt-Allender double counting](reinhardt-allender-double-counting.md)

## Proof depends on

- [Unique double-counting transcripts characterize min-unique rounds](double-counting-transcript-uniqueness.md)

## Sources

- K. Reinhardt and E. Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
