# Greedy valid plane tree and connectivity of the local-move graph

**Setting.** A *plane tree* with $n$ edges models an RNA secondary structure: its $2n$ half-edges are labelled $1,\dots,2n$ counterclockwise from the root, and each edge $e(i,j)$ pairs half-edges $i<j$ (edges are non-crossing and $i,j$ have opposite parity). A *complementary alphabet* $\mathcal A$ has an involution $B\mapsto\overline B$ with $\overline B\ne B$ (e.g. the Watson–Crick pairs). For a word (primary sequence) $P=p_1\cdots p_{2n}$ over $\mathcal A$, a plane tree $S$ is **$P$-valid** if $p_i$ and $p_j$ are complementary for every edge $e(i,j)$; $\mathcal V(P)$ denotes the set of $P$-valid trees. For $i<j<i'<j'$, a *type 1 local move* replaces adjacent edges $e(i,j),e(i',j')$ by $e(i,j'),e(j,i')$, and a *type 2 local move* is its inverse. A move is *valid* if it maps $\mathcal V(P)$ to $\mathcal V(P)$.

**Greedy algorithm.** Read $P$ left to right with a stack: push $p_1$; for each later $p_i$, pop the top letter if it is $\overline{p_i}$, otherwise push $p_i$. Record a pair $(i,j)$ whenever $p_i$ is popped at step $j$.

**Theorem.** Let $\mathcal G_P$ be the graph on $\mathcal V(P)$ whose edges are valid local moves, and $\mathcal G_P^+$ its orientation along type 2 moves.

1. If $\mathcal V(P)\ne\varnothing$, the greedy algorithm ends with an empty stack and its pairs form a $P$-valid plane tree $T_0$.
2. $\mathcal G_P$ is connected.
3. $\mathcal G_P^+$ has no directed cycles, and $T_0$ is its unique sink: every $T\in\mathcal V(P)$ other than $T_0$ admits a valid type 2 move, and a path of type 2 moves leads from every $T$ to $T_0$.
4. $T_0$ is characterized equivalently as the unique sink of $\mathcal G_P^+$, as the output of the greedy algorithm, and as the $P$-valid tree of minimum total distance $d_T=\sum_{v\in T}\operatorname{dist}(v,v_0)$ to the root $v_0$.

## Expansion

A valid type 1 move on adjacent edges $e(i,j),e(i',j')$ exists exactly when $p_i=p_{i'}=B$ and $p_j=p_{j'}=\overline B$ for some letter $B$, and the same letter condition characterizes valid type 2 moves on $e(i,j'),e(j,i')$. A type 2 move strictly decreases the total root distance, which rules out directed cycles. The greedy algorithm closes each pair as early as possible, so a valid tree that differs from $T_0$ contains a pair that could have been closed earlier; this yields a type 2 move toward $T_0$. Connectivity then follows because every tree reaches the same sink. Biologically, the greedy tree models co-transcriptional folding, in which the molecule forms its first base pairs as soon as complementary letters meet.

## Sources

- Frances Black, Elizabeth Drellich, Julianna Tymoczko, "Valid plane trees: Combinatorial models for RNA secondary structures with Watson-Crick base pairs", arXiv:1501.03238 (2015), Definitions of local moves, $P$-valid plane trees and the greedy algorithm (Sections 2–3), Proposition 2.7, Theorems 3.4, 3.6–3.7, Corollaries 3.5, 3.8, 3.10–3.11, <https://doi.org/10.48550/arXiv.1501.03238>.
