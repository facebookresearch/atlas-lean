# Diploid path graph of read bipartitions

**Setting.** Let $M$ be an $m\times n$ alignment matrix of reads (rows) against variant sites (columns), with $M_{i,j} \in \Sigma_j \cup \{-\}$, where $-$ means read $i$ is uninformative at site $j$; no row or column is all gaps. Row $i$ is **active** at column $j$ if its first non-gap entry is at or before $j$ and its last at or after $j$; it is **terminal** at $j$ if its last non-gap entry is at $j$ (or $j = n$). Let $A_j$ be the active rows and $A'_j$ the active non-terminal rows of column $j$; $\mathcal B_j$ and $\mathcal C_j$ denote the sets of bipartitions $(B^1,B^2)$ of $A_j$ and of $A'_j$. Bipartitions $B, C$ are **compatible** if $B^1 \cap (C^1\cup C^2) \subseteq C^1$ and $B^2 \cap (C^1 \cup C^2) \subseteq C^2$.

The directed graph $G$ has vertices $\{\mathrm{start},\mathrm{end}\} \cup \bigcup_j(\mathcal B_j \cup \mathcal C_j)$ and edges $B_j \to C_j$ and $C_j \to B_{j+1}$ between compatible bipartitions, plus $\mathrm{start} \to \mathcal B_1$ and $\mathcal B_n \to \mathrm{end}$. A start-to-end path $D$ is a **diploid path**; the unions of the first and second parts of its vertices form a bipartition $B_D$ of all rows.

**Lemma.** The map $D \mapsto B_D$ is a bijection between diploid paths and the $2^m$ bipartitions of the rows of $M$.

**Size.** With $\mathrm{maxCov} = \max_j |A_j|$, $G$ has at most $2 + (2n-1)\,2^{\mathrm{maxCov}}$ vertices and at most $2n\,2^{\mathrm{maxCov}}$ edges.

## Expansion

Each $B_j$ has in- and out-degree $1$, and all members of $\mathcal C_j$ have the same in-degree $2^{|A_j| - |A'_j|}$, one choice of side for each row that terminates at $j$. Distinct diploid paths must differ at some $\mathcal B_j$ or $\mathcal C_j$ and then induce different bipartitions, giving injectivity. Counting paths backwards from the end vertex gives $\prod_j 2^{|A_j| - |A'_j|} = 2^m$, because every row is active and terminal in exactly one column; so the map is also surjective. The graph is exponential only in local coverage, not in the number of reads, which is what makes exact inference over read bipartitions (the probabilistic analogue of weighted minimum error correction) tractable for long reads.

## Sources

- J. Ebler, M. Haukness, T. Pesout, T. Marschall, B. Paten, "Haplotype-aware diplotyping from noisy long reads", Genome Biology 20 (2019) 116, Methods (alignment matrix; a graphical representation of read partitions), Lemma 1 and its proof, <https://doi.org/10.1186/s13059-019-1709-0>, PMCID PMC6547545.
