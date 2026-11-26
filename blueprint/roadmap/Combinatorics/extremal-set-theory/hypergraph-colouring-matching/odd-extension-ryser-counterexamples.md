# Ryser counterexamples in odd extension degrees

For a rank $r$, call a witness a nonempty finite intersecting hypergraph on a finite vertex set with $r>0$, a part map to $r$ labels with exactly one vertex of every label on each edge, all edges of size $r$, a vertex cover, matching number one, and cover number $r>(r-1)\nu$. There is a prime threshold $P$ such that each prime $p\ge P$ with $p\equiv2\pmod3$ has a degree threshold $D_p\ge3$ and supplies a witness of rank $p^n+1$ for every odd $n\ge D_p$.

## Depends on

- Finite matchings and covers, labelled parts and r-uniformity.

## Proof outline

State the construction and its witness checks separately, retaining the per-prime threshold. This supplies the proof prerequisite for the associated infinite-ranks result.

- Odd-extension finite-field construction, with proofs of intersection and the lower bound on cover size.

## Sources

- [Comparator statement: `OAI.RyserOdd.eventualOddFailures_and_infinite`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RyserOddExtensions.lean#L61-L69)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/162.md)
