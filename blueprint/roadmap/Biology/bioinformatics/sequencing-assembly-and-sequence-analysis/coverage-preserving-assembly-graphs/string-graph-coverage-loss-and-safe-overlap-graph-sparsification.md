# String-graph coverage loss and safe overlap-graph sparsification

Use the setting of coverage-preserving assembly graphs: reads $R$, coverage parameters $l_1 > l_2$, length bound $\phi$, candidate genomes $C(R, l_1, l_2, \phi)$, and the overlap graph $O_k(R)$ with $k \le l_2$, which spells every candidate. The **string graph** $S_k(R)$ keeps only the longest overlap per read pair, deletes **contained reads** (reads that are substrings of another read), and removes transitive arcs.

**Observation (string graphs are not coverage-preserving).** For no $k$ is $S_k(R)$ guaranteed to be coverage-preserving. With $l_1 = 6$, $l_2 = 2$, $\phi = 10$ and reads $R = \{\mathtt{CACGTG}, \mathtt{CACGTGG}, \mathtt{TGTGCA}, \mathtt{TGGGCA}\}$, both $\langle \mathtt{CACGTGTG} \rangle$ and $\langle \mathtt{CACGTGGG} \rangle$ are candidates, but $\mathtt{CACGTG}$ is contained in $\mathtt{CACGTGG}$ and is removed, so the first candidate can no longer be spelled.

Let $O'$ be any subgraph of $O_k(R)$ obtained by safe operations and let $W_\phi(G)$ be the set of circular strings of length at most $\phi$ spelled by $G$. An operation is **safe** if it preserves all candidates.

- **Lemma 5.** A vertex $u$ can be removed safely if $W_\phi(O') = W_\phi(O' - u)$; **Lemma 6** is the same statement for a single arc.
- **Lemma 7 (transitive reduction).** If arcs $e_1 : v_1 \to v_2$, $e_2 : v_2 \to v_3$ and $e_3 : v_1 \to v_3$ satisfy $w(e_1) + w(e_2) = w(e_3)$, where $w$ is the length of the non-overlapping prefix, then $e_3$ can be removed safely.
- **Lemma 8 (contained reads).** The vertex of a contained read $r$ can be removed safely if $r$ is a substring of exactly one candidate $z$, $r$ matches a non-repetitive substring of $z$, and $O'$ still contains a vertex of some parent read of $r$.

## Depends on

- [Coverage-preserving de Bruijn and overlap graphs](coverage-preserving-de-bruijn-and-overlap-graphs.md)

## Expansion

The counterexample shows that the contained-read rule, not transitive reduction, is what breaks coverage: a short read can be the only witness of one haplotype while being a substring of a read from the other. Lemma 7 holds because any walk using $e_3$ can be rerouted through $v_2$ and spell the same string. For Lemma 8, any candidate containing $r$ must be $z$, so the parent read also occurs only in $z$; a closed walk spelling $z$ that passes through $r$ visits it once (non-repetitive), and the walk can be rerouted through the parent read covering the same positions. These lemmas give a coverage-preserving alternative to the string graph: transitive sparsification of the overlap multigraph plus removal of contained reads only when they are haplotype-specific and non-repetitive, with remaining contained reads filtered by checking that the $k$-mers of bounded walks through the read are already present in walks through its parents.

## Sources

- C. Jain, "Coverage-preserving sparsification of overlap graphs for long-read assembly", Bioinformatics (2023), Section 2.3 (coverage assumption and Definition), Section 3 (Theorems 1 and 2, Lemmas 1-4, Observation), Section 4 (Lemmas 5-8). <https://doi.org/10.1093/bioinformatics/btad124> (PMC10132763)
