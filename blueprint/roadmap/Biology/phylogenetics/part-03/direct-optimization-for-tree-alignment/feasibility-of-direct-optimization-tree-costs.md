# Feasibility of direct optimization tree costs

**Tree alignment problem.** Given a rooted binary tree $T = (V,E)$, an alphabet $\Sigma$ containing an indel symbol, a distance $d$ on $\Sigma$, and sequences $\chi(v) \in \Sigma^*$ at the leaves, find an extension $\chi'$ of $\chi$ to all vertices minimizing $\sum_{(u,v)\in E} e(\chi'(u),\chi'(v))$, where $e$ is the (Needleman–Wunsch) edit distance

$$e(A_{1..i},B_{1..j}) = \min\{e(A_{1..i-1},B_{1..j-1}) + d(A_i,B_j),\ e(A_{1..i-1},B_{1..j}) + d(A_i,\text{indel}),\ e(A_{1..i},B_{1..j-1}) + d(B_j,\text{indel})\}.$$

**Reduced alignment graphs.** Let $\Sigma_P = \mathcal P(\Sigma)\setminus\{\emptyset\}$. A reduced alignment graph (RAG) is a string $A \in \Sigma_P^*$; it contains every sequence obtained by choosing one element from each set and deleting indels, so it contains at most $\prod_{X\in A}|X|$ sequences. With $d_P(X,Y) = \min_{x\in X, y\in Y} d(x,y)$, the RAG edit distance $e_P$ is the recursion above with $d$ replaced by $d_P$. For aligned RAGs $A,B$ of equal length, the median RAG is $m_P(A,B) = \langle m(A_i,B_i)\rangle_i$, where $m(X,Y)$ is the set of elements of $X$ and $Y$ realizing $d_P(X,Y)$. Assume a linear indel cost: $d(x,\text{indel}) = b$ for all $x \ne \text{indel}$.

**Lemma.**
1. For RAGs $A,B$ there are sequences $U$ in $A$ and $V$ in $B$ with $e_P(A,B) = e(U,V)$, found by backtracking in $O(n^2)$ time.
2. If $C = m_P(A,B)$, then for every sequence $X$ in $C$ there are $Y$ in $A$ and $Z$ in $B$ with $e_P(A,B) = e(Y,Z) = e(X,Y) + e(X,Z)$.

**Theorem.** Direct optimization assigns to each leaf $v$ its leaf sequence $S(v)$, and $S(v) = m_P(U,W)$ to an internal vertex with children $u,w$, where $U,W$ is an optimal alignment of $S(u),S(w)$, and returns $\mathrm{DO}(T,\chi) = \sum_{v \text{ internal}} e_P(S(u),S(w))$. There is an assignment $\chi'$ agreeing with $\chi$ on the leaves such that

$$\mathrm{DO}(T,\chi) = \sum_{(u,v)\in E} e(\chi'(u),\chi'(v)),$$

so the returned cost is an upper bound on the optimal tree alignment cost. It runs in $O(n^2|V|)$ time for small alphabets ($O(n^2|V||\Sigma|)$ otherwise), with $n$ the maximum sequence length.

**Affine gaps.** For affine indel costs $G(k) = a + bk$ the median property (Lemma 2) fails, and using $e_P$ directly can report costs that no assignment achieves; a modified pairwise RAG alignment with four dynamic-programming matrices (Affine-DO) restores the guarantee that some compatible assignment has cost at most the reported value, with the same time complexity.

## Depends on

- [The Needleman–Wunsch recurrence](../../../bioinformatics/sequence-alignment/pairwise-sequence-alignment/nw-score-eq.md)

## Expansion

Feasibility is shown by a pre-order backtrack: pick any sequence in the root's RAG, then at each child pick a contained sequence closest to the parent's choice. Lemma 2 guarantees that whatever was chosen at the parent, the children's choices realize exactly the cost $e_P$ charged at that vertex, so the charges add up to the cost of a concrete assignment. Under affine costs, choosing a sequence inside a median RAG can split an indel block and incur an extra gap opening not counted by $e_P$; Affine-DO tracks gap openings in the RAG alignment and proves feasibility by a credit–debit induction over subtrees.

## Sources

- A. Varón, W. C. Wheeler, "The tree alignment problem", BMC Bioinformatics 13:293 (2012), Eq (1), Observations 1–2, Lemmas 1–2, Definition 1, Theorem 1, Eqs (2)–(5) and Theorems 3–4, <https://doi.org/10.1186/1471-2105-13-293>, PMCID PMC3605350.
