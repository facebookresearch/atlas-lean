# Unsafe unitigs under incomplete coverage

Strings are over $\{A, C, G, T\}$; $\mathrm{pre}_k(x)$ and $\mathrm{suf}_k(x)$ are the first and last $k$ characters of $x$, $\mathrm{occ}_y(x)$ the number of occurrences of $x$ in $y$, and $\mathrm{sp}_k(x)$ the set of $k$-mers of $x$. The **basic de Bruijn graph** $G_{\mathrm{basic}}(K)$ on a $k$-mer set $K$ has an edge $x \to y$ whenever $\mathrm{suf}_{k-1}(x) = \mathrm{pre}_{k-1}(y)$. A walk $w = (x_0, \dots, x_m)$ is a **unitig** if it is not a periodic cycle, $d^-(x_i) = 1$ for $1 \le i \le m$ and $d^+(x_i) = 1$ for $0 \le i \le m-1$; its spelling glues consecutive $k$-mers along their $(k-1)$-overlaps.

Error-free reads induce **sequenced segments** $\mathcal S = \{S_1, \dots\}$: the strings of the maximal genomic intervals covered by reads with consecutive reads overlapping by at least $k-1$. A unitig $w$ of $G_{\mathrm{basic}}(\mathrm{sp}_k(\mathcal S))$ is **unsafe** if its spelling is not a substring of any $S \in \mathcal S$ (a potential misassembly).

**Theorem.** A unitig $w = (x_0, \dots, x_m)$ of $G_{\mathrm{basic}}(\mathrm{sp}_k(\mathcal S))$ is unsafe if and only if for every $S \in \mathcal S$ one of the following holds:
1. $S$ contains no $k$-mer of $w$;
2. $\mathrm{occ}_S(\mathrm{pre}_k(S)) = 1$ and $\mathrm{pre}_k(S) = x_i$ for some $1 \le i \le m$;
3. $\mathrm{occ}_S(\mathrm{suf}_k(S)) = 1$ and $\mathrm{suf}_k(S) = x_j$ for some $0 \le j \le m-1$;
4. $\mathrm{occ}_S(\mathrm{pre}_k(S)) = \mathrm{occ}_S(\mathrm{suf}_k(S)) = 2$ and $\mathrm{pre}_k(S) = x_i$, $\mathrm{suf}_k(S) = x_j$ for some $1 \le i \le j \le m-1$.

**Corollary (perfect coverage).** For a single string $X$ and a unitig $w$ of $G_{\mathrm{basic}}(\mathrm{sp}_k(X))$, the spelling of $w$ is not a substring of $X$ if and only if either $\mathrm{occ}_X(\mathrm{pre}_k(X)) = \mathrm{occ}_X(\mathrm{suf}_k(X)) = 1$ with $\mathrm{pre}_k(X) = x_i$ and $\mathrm{suf}_k(X) = x_{i-1}$ for some $1 \le i \le m$, or both occur exactly twice with $\mathrm{pre}_k(X) = x_i$, $\mathrm{suf}_k(X) = x_j$ for some $0 < i \le j < m$. At most one unitig of $G_{\mathrm{basic}}(\mathrm{sp}_k(X))$ can be unsafe.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

Every $k$-mer of the graph lies in some segment, and a segment's walk can only enter or leave the interior of a unitig through its own first or last $k$-mer, since interior unitig vertices have in- and out-degree one. A segment fails to contain $w$ exactly when its walk starts inside $w$ without returning to its start (case 2), ends inside $w$ (case 3), or starts and ends inside $w$ in a configuration visiting those vertices twice (case 4). The typical genomic mechanism is a repeat whose copy boundaries fall in unsequenced regions: the repeat's unitig loses its branching neighbours and is extended into a longer unitig that the genome does not contain. Raising coverage or breaking unitigs where coverage drops removes these misassemblies.

## Sources

- A. Rahman, P. Medvedev, "Assembler artifacts include misassembly because of unsafe unitigs and underassembly because of bidirected graphs", Genome Research 32(9) (2022) 1746–1753, Methods ("Safety of unitigs"), Theorem 1 and Corollary 1, <https://doi.org/10.1101/gr.276601.122>, PMCID PMC9528984.
