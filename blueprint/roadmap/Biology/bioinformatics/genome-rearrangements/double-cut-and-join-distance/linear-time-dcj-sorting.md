# Linear-time double-cut-and-join sorting algorithm

Given two genomes $A$ and $B$ on the same set of $N$ genes, an optimal double-cut-and-join
sorting sequence of length $d_{\mathrm{DCJ}}(A, B) = N - (C + I/2)$ can be computed in
$O(N)$ time (Algorithm 2 of Bergeron, Mixtacki and Stoye).

## Depends on

- [Double-cut-and-join distance formula](dcj-distance.md)
- [Num Cycles](num-cycles.md)
- [Num Odd Paths](num-odd-paths.md)

## Expansion

A sound expansion has separate pages for:

1. **Genome representation** (Section 4, Tables 1 and 2). A table of the adjacencies and telomeres
   of $A$, with two rows and at most $2N$ columns, and a table giving for each gene the columns that
   hold its head and its tail, so that the adjacency or telomere containing a gene extremity is
   found, and replaced, in constant time.
2. **Greedy sorting** (Algorithm 2). For each adjacency $\{p, q\}$ of $B$ whose extremities lie in
   different elements $u \ne v$ of $A$, replace $u$ and $v$ by $\{p, q\}$ and, only if it is
   nonempty, by $(u \setminus \{p\}) \cup (v \setminus \{q\})$ (two telomeres $u = \{p\}$ and
   $v = \{q\}$ give $\{p, q\}$ alone); then, for each telomere $\{p\}$ of $B$ that lies in
   an adjacency $u$ of $A$, replace $u$ by $\{p\}$ and $u \setminus \{p\}$. Each replacement is a DCJ
   operation, and the result is $B$.
3. **Optimality** (Lemma 4 and Theorem 1). Each replacement increases $C + I/2$ by one, as it
   creates a cycle of length two or two odd paths of length one, while no DCJ operation increases
   it by more than one; so the sequence has length $N - (C + I/2) = d_{\mathrm{DCJ}}(A, B)$.
4. **Running time** (proof of Theorem 1). With the representation of step 1 each replacement is
   found and performed in constant time, and there are at most $d_{\mathrm{DCJ}}(A, B) \le N$ of
   them, so the procedure runs in $O(N)$ time.

## Sources

- A. Bergeron, J. Mixtacki and J. Stoye, A unifying view of genome rearrangements, in
  Algorithms in Bioinformatics (WABI 2006), Lecture Notes in Bioinformatics 4175, Springer,
  2006, 163–173, Section 4 (Tables 1 and 2), Algorithm 2, Lemma 4 and Theorem 1.
  <https://doi.org/10.1007/11851561_16>
