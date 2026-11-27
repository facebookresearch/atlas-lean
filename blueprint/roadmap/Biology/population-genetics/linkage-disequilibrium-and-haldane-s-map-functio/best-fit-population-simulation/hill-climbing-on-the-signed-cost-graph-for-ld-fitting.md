# Hill climbing on the signed cost graph for LD fitting

**Problem $k$-CMP.** Given an $n \times k$ binary haplotype matrix with assigned marker columns $j_1, \dots, j_k$, construct a new column $j_{k+1}$ with prescribed minor allele frequency $p_{k+1}$ whose pairwise linkage disequilibrium with each column $j_l$ fits a target. With $Q_{10}$ the number of rows showing pattern $10$ in columns $(j_l, j_{k+1})$, the observed LD is $D^{\mathrm{obs}}_l = \tfrac1n\left(np_l(1 - p_{k+1}) - Q_{10}\right)$, and the targets are integer deviations $G_l = nD^{\mathrm{target}}_l$.

**Signed cost graph.** Nodes are the $2^k$ patterns $Z$ of the first $k$ columns; $f(Z)$ and $t(Z)$ count rows with pattern $Z$ and a $0$, respectively $1$, in column $j_{k+1}$. An edge $Z_1 \to Z_2$ carries the $k$-tuple $(c(Z_1[l], Z_2[l]))_l$ with $c(0,1) = -1$, $c(1,0) = +1$, $c(0,0) = c(1,1) = 0$. The move $\mathrm{Move}(Z_1 \to Z_2, x)$, $0 \le x \le \min(f(Z_1), t(Z_2))$, swaps $x$ ones from pattern-$Z_2$ rows to pattern-$Z_1$ rows in the new column and updates $G_l \mathrel{+}= x\,c(Z_1[l], Z_2[l])$. The signed cost graph keeps only edges that strictly improve every target in the direction of its sign.

**Facts (Parida and Haiminen 2015).**

1. For every $k$, the signed cost graph is acyclic (Lemma 1).
2. Every move preserves $f(Z) + t(Z)$ for each $Z$ and $\sum_Z t(Z) = n_1$, so the minor allele frequency of the new column always equals its input exactly (Lemma 2, Corollary 1).
3. Each marker is fitted in $O(n)$ time, so a full $m$-marker matrix is produced in time linear in the output size (Lemma 3).

## Depends on

- [Gametic linkage disequilibrium](../../../quantitative-genetics/dominance-linkage-disequilibrium/ld-d.md)

## Expansion

Along an edge with nonpositive cost the move turns $0 \to 1$ only towards $-1$ and $1 \to 0$ only towards $+1$; once a coordinate changes sign it cannot change back, so no directed cycle exists. Acyclicity means no move is ever undone, every cell of the new column is touched at most twice, and with hashing each candidate cell is found in constant time. The number of ones moved is bounded by $p_{k+1}n$ because $|D^{\mathrm{target}}_l| \le p_{k+1}$.

## Sources

- L. Parida and N. Haiminen, *SimBA: simulation algorithm to fit extant-population distributions*, BMC Bioinformatics 16 (2015), 82, Problem $k$-CMP, Eqs. (5)–(9), Lemmas 1–3 and Corollary 1. <https://doi.org/10.1186/s12859-015-0525-0> (PMCID: PMC4372275)
