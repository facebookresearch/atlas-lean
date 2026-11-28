# Ryser counterexamples for one prime and all large prime extension degrees

There is a prime $p>5$ with $p\equiv2\pmod3$ and a threshold $N$ such that for every prime $n\ge N$ with $n>2$, rank $r=p^n+1$ admits a finite nonempty hypergraph with the following properties. Each edge has exactly one vertex of each of the $r$ parts; distinct edges intersect. There is a cover by vertices, the minimum cover size is $r$, and the maximum number of pairwise disjoint edges is one. Thus this witness fails Ryser's bound $\tau\le(r-1)\nu$.

## Depends on

- Part map to r labels, finite nonempty edge set, matching and vertex-cover extrema.

## Proof outline

Separate the finite-field construction and its threshold choices from the extremal checks on every graph. Do not replace existential fixed $p$ by a numerical assertion or generalize prime $n$ to odd degrees for this particular $p$.

- Existence of a single characteristic and the cover and intersection estimates uniform over sufficiently large prime extension degrees.

## Sources

- [Comparator statement: `OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RyserCovering.lean#L49-L54)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/162.md)
