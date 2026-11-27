# Independent-set lower bound for join queries

Let $q = R_1 \bowtie \dots \bowtie R_n$ be a join query and $V$ an [independent set](fractional-independent-sets-of-a-hypergraph.md)
of its hypergraph. Then for every $k \in \mathbb N$ there is a database $D$ in which every relation has at most $k$ tuples and

$$k^{|V|} \le |q(D)|.$$

For the triangle query and $V = \{A\}$ this is the database with $R = \{(i, 1)\}$, $S = \{(1, 1)\}$ and $T = \{(1, i)\}$ for
$i \in [k]$, which has $k$ answers. The tight version, with fractional independent sets matching the
[AGM bound](../join-processing/agm-output-size-bound-for-join-queries.md), is the first item of the AGM tightness node.

## Depends on

- [Natural join queries, their hypergraphs and fractional edge covers](../join-processing/natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)
- [Fractional independent sets of a hypergraph](fractional-independent-sets-of-a-hypergraph.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 25.5 and the preceding example (pp. 209–210).
