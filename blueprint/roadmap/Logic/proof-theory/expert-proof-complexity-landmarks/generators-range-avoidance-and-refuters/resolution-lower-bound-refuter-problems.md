# Refuter problems for resolution lower bounds

The refuter problem of a resolution lower bound takes a purported resolution refutation that is shorter (or narrower) than the bound allows and asks for one invalid derivation step. It is a total search problem exactly when the lower bound is true, so its complexity measures how hard the lower bound is to prove.

**Resolution refutations as inputs.** Let $F$ be an unsatisfiable CNF with $n$ variables and $m$ clauses, called axioms and indexed $C_{-m},\dots,C_{-1}$. A (purported) resolution refutation of $F$ is a sequence of nodes $C_0,\dots,C_{L-1}$, where node $C_i$ stores

- a set of literals over $x_1,\dots,x_n$ (also read as the clause $C_i$),
- a tag, "resolution" or "weakening",
- for "resolution": indices $-m\le j,k<i$ and a variable $a\in\{1,\dots,n\}$; for "weakening": one index $-m\le j<i$.

Node $C_i$ is a valid derivation if: when tagged "resolution", there are clauses $D,E$ with $C_j=x_a\lor D$, $C_k=\overline{x}_a\lor E$ and $C_i=D\lor E$; when tagged "weakening", $C_i=C_j\lor D$ for some clause $D$. The refutation is valid if every node is a valid derivation and $C_{L-1}=\bot$. Its length (size) is $L$, and its width is the largest number of literals in a clause $C_i$, $-m\le i<L$.

**Refuter problems.** Let $\mathcal F=\{F_n\}_{n\in\mathbb N}$ be a family of unsatisfiable CNFs such that every resolution refutation of $F_n$ has width greater than $w_n$ and size greater than $s_n$.

- An input to $\mathrm{Refuter}(w(F_n\vdash_{\mathrm{Res}}\bot)\le w_n)$ is a purported resolution refutation of $F_n$ of width at most $w_n$ (each node is allotted only $w_n$ literals).
- An input to $\mathrm{Refuter}(s(F_n\vdash_{\mathrm{Res}}\bot)\le s_n)$ is a purported resolution refutation of $F_n$ with at most $s_n$ clauses.

In both problems a solution is an index $i$ such that node $C_i$ violates the validity conditions above (an invalid derivation).

The problems live in the decision-tree model of total search: the input is accessed by queries, each node is a block of $\mathrm{poly}(w,\log n,\log L)$ bits, and efficiency is measured by the number of blocks queried (block-depth). Whether a given node is an invalid derivation can be checked with block-depth at most 3, so both refuter problems are in $\mathsf{FNP}^{\mathrm{dt}}$, and they are total, hence in $\mathsf{TFNP}^{\mathrm{dt}}$, whenever the lower bound $w_n$ or $s_n$ is true.

## Expansion

A purported refutation that beats a true lower bound cannot be valid, so an error must exist; the refuter problem asks to locate it. The typical regime has length exponential in the width, $L=2^{w^{\Omega(1)}}$, so that each block costs only polylogarithmically many bit queries, and $L=2^{n^{O(1)}}$. The width version of the pigeonhole principle refuter is trivial because $\mathrm{PHP}_{(n+1)\to n}$ already has an axiom of width $n$; the source instead uses a constant-width encoding with an $n/3$ width lower bound, or monotone width.

Refuter problems for lower bounds against algorithms and circuits were studied before; this formulation transfers the idea to proof complexity, where a reduction of the refuter problem to a syntactic class such as $\mathsf{PLS}$ amounts to proving the lower bound in the corresponding fragment of bounded arithmetic.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

None.

## Sources

- Jiawei Li, Yuhao Li, Hanlin Ren, "Finding Bugs in Short Proofs: The Metamathematics of Resolution Lower Bounds", *STOC* 2026, arXiv:2411.15515v2, https://arxiv.org/abs/2411.15515 (Definitions 3.5 and 3.6, Section 3.2, Section 3.4, Problem 1.1).
