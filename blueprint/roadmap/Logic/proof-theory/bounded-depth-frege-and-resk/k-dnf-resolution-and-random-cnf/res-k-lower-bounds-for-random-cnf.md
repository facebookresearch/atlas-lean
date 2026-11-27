# Res($k$) lower bounds for random CNFs

With high probability, random $\Delta$-CNFs need Res($k$) refutations of size $2^{n^{\delta}}$: for $m\le\eta n$ clauses and $k\le\nu\sqrt{\log n}$, for $m\le n\log^h n$ and $k\le\nu\sqrt{\log n/\log\log n}$, and for every constant $k$ when $m\le n^h$, with $\Delta$ a large enough constant.

Let $\varphi(m,n,\Delta)$ be the distribution of random $\Delta$-CNFs on $n$ variables obtained by sampling $m$ clauses uniformly with replacement from the $\binom{n}{\Delta}2^{\Delta}$ possible clauses. For $\Delta\ge3$ such a formula is unsatisfiable with high probability when $m\ge\ln2\cdot2^{\Delta}n$; refutations exist only for unsatisfiable formulas.

**Theorem.** In each case "whp" means with probability $1-o(1)$ over $\varphi\sim\varphi(m,n,\Delta)$, and size is the number of lines of a [Res($k$)](k-dnf-resolution.md) proof.

1. For any $\eta>0$ there is $\Delta>0$ such that if $m\le\eta n$, then there are constants $\delta,\nu>0$ such that whp every Res($k$) proof of $\varphi$ has size at least $2^{n^{\delta}}$ whenever $k\le\nu\sqrt{\log n}$.
2. For any $h>0$ there is $\Delta>0$ such that if $m\le n\log^h n$, then there are constants $\delta,\nu>0$ such that whp every Res($k$) proof of $\varphi$ has size at least $2^{n^{\delta}}$ whenever $k\le\nu\sqrt{\log n/\log\log n}$.
3. For any $h>0$ there is $\Delta>0$ such that if $m\le n^h$, then for every constant $k$ there is a constant $\delta>0$ such that whp every Res($k$) proof of $\varphi$ has size at least $2^{n^{\delta}}$.

## Expansion

Each case shows that the dependency graph is whp an $(r,\Delta,0.95\Delta)$-boundary expander, with $r=\delta n$ in case 1, $r=n/\log^{\ell}n$ in case 2 and $r=n^{1-\delta'}$ in case 3, and checks the condition of the [boundary-expansion lower bound](res-k-lower-bound-from-boundary-expansion.md). Boundary expansion comes from ordinary vertex expansion of the random dependency graph by unique-neighbour counting: $|N(S)|\le|\partial(S)|+(\Delta|S|-|\partial(S)|)/2$, so expansion $(1-\varepsilon)\Delta$ gives boundary expansion $(1-2\varepsilon)\Delta$. Case 3 improves the Segerlind-Buss-Impagliazzo exponential lower bound, which needed $m=O(n^{7/6})$ and $\Delta=O(k^2)$, and gives the first Res($k$) bound for clause density $m/n>n^{1/6}$ with $\Delta$ independent of $k$; case 1 improves Alekhnovich's range $k=O(\sqrt{\log n/\log\log n})$ for $m=O(n)$. The constant $\Delta$ must be large (the source estimates about $100$) for the expansion to hold. For resolution itself, random $k$-CNFs at constant density need [exponential size](../../resolution-separations-and-supercritical-tradeoffs/chvatal-szemeredi-random.md).

## Depends on

- [k-DNF resolution Res(k)](k-dnf-resolution.md)

## Proof depends on

- [Res(k) lower bounds from boundary expansion](res-k-lower-bound-from-boundary-expansion.md)
- [Unique-neighbour lemma for bipartite vertex expanders](../../../../GraphTheory/algebraic-graph-theory/spectral-expansion-and-connectivity/unique-neighbour-lemma.md)

## Sources

- Anastasia Sofronova and Dmitry Sokolov, "A Lower Bound for k-DNF Resolution on Random CNF Formulas via Expansion", *40th Computational Complexity Conference (CCC 2025)*, LIPIcs vol. 339, paper 32, 2025, https://doi.org/10.4230/LIPIcs.CCC.2025.32; numbering as in the [ECCC Report TR22-054 edition](https://eccc.weizmann.ac.il/report/2022/054/) (Definition 4.1, Lemma 4.2, Theorems 6.1, 6.2 and 6.3, Sections 1.1-1.2; Appendix C, expansion of random dependency graphs).
