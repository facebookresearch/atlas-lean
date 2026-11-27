# Maximal unitigs of doubled versus bidirected de Bruijn graphs

Let $K$ be a set of canonical $k$-mers with $k$ odd (so no $k$-mer is its own reverse complement $\bar x$). The **doubled de Bruijn graph** $G_{\mathrm{dbl}}(K) = G_{\mathrm{basic}}(K \cup \bar K)$ is the basic directed graph on all $k$-mers and their reverse complements. The **bidirected de Bruijn graph** $G_{\mathrm{bid}}(K)$ has one vertex per $k$-mer of $K$, each with two sides $(u, 0), (u, 1)$, and an undirected edge $\{(u_0, s_0), (u_1, s_1)\}$ for every oriented overlap $\mathrm{suf}(\mathrm{orient}(x_0, 1 - s_0)) = \mathrm{pre}(\mathrm{orient}(x_1, s_1))$, where $\mathrm{orient}(x, 0) = x$ and $\mathrm{orient}(x, 1) = \bar x$. A walk enters each vertex on one side and leaves on the other; a unitig requires every internal side to have degree one, an **inverted loop** is an edge joining a side to itself, and it is **lonely** if it is the only edge at that side.

Partition the maximal unitigs of $G_{\mathrm{dbl}}(K)$ into nonpalindromic $D_{\text{non-pal}}$ and palindromic $D_{\text{pal}}$ (spelling equal to its reverse complement), and those of $G_{\mathrm{bid}}(K)$ into $B_{\text{no-loop}}$, $B_{\text{first-loop}}$ and $B_{\text{last-loop}}$ according to which endpoint side carries a lonely inverted loop.

**Theorem.** Suppose $G_{\mathrm{dbl}}(K)$ has no circular unitig. Then
1. the walk map $F_W$, sending each $k$-mer $x$ to the vertex side $(u, s)$ with $\mathrm{orient}(\mathrm{lab}(u), s) = x$, is a spelling-preserving bijection from $D_{\text{non-pal}}$ to $B_{\text{no-loop}}$;
2. reversal is a bijection between $B_{\text{last-loop}}$ and $B_{\text{first-loop}}$;
3. the map $\mathrm{head}$, taking the first half of a palindromic maximal unitig, is a bijection from $D_{\text{pal}}$ to $B_{\text{last-loop}}$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

$F_W$ is a bijection between vertices of the doubled graph and vertex sides of the bidirected graph, maps each pair of mirror edges $(x, y), (\bar y, \bar x)$ to one bidirected edge, and hence is a spelling-preserving bijection on walks. Unitig maximality is preserved except at a self-mirror edge $x \to \bar x$ (when $\mathrm{suf}(x) = \overline{\mathrm{suf}(x)}$), which becomes a lonely inverted loop: a palindromic maximal unitig through it in the doubled graph is cut into its two halves in the bidirected graph, each ending at the loop and reverses of one another. So the bidirected model offers no advantage for unitig construction and underassembles at long exact palindromes unless unitigs are allowed to continue through inverted loops; when no such $k$-mers exist, $D_{\text{pal}}$, $B_{\text{first-loop}}$ and $B_{\text{last-loop}}$ are empty and the two graphs have the same maximal unitigs.

## Sources

- A. Rahman, P. Medvedev, "Assembler artifacts include misassembly because of unsafe unitigs and underassembly because of bidirected graphs", Genome Research 32(9) (2022) 1746–1753, Methods (bidirected graph definitions, relationship between doubled and bidirected graphs), Theorem 2, <https://doi.org/10.1101/gr.276601.122>, PMCID PMC9528984.
