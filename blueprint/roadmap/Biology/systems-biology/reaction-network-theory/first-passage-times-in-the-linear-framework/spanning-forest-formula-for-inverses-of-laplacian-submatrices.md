# Spanning-forest formula for inverses of Laplacian submatrices

**Setting.** A linear-framework graph $G$ is a finite, simple, directed graph on vertices
$\{1,\dots,N\}$ with positive edge labels $\ell(i \to j)$ (transition rates), connected when edge
directions are ignored. Its Laplacian has entries $L(G)_{ij} = \ell(j \to i)$ for $i \ne j$ with
$j \to i$, $0$ for other $i \ne j$, and $L(G)_{jj} = -\sum_k \ell(j \to k)$, so the master equation is
$\dot x = L(G) x$. The weight $w(H)$ of a subgraph is the product of its edge labels, and the weight of a
set of subgraphs is the sum of their weights. A **spanning forest** contains every vertex, no cycle
(ignoring directions), and at most one outgoing edge per vertex; its roots are the vertices without
outgoing edge. $\Phi_A(G)$ is the set of spanning forests rooted exactly at $A$, and for $\#A = \#B$,
$\Phi_{B \to A}(G) \subseteq \Phi_A(G)$ consists of those in which each vertex of $B$ has a path to a
distinct root in $A$.

**All-Minors Matrix-Tree theorem.** For proper nonempty $A, B \subsetneq V(G)$ with $\#A = \#B = k$,
listed increasingly as $a_1<\dots<a_k$ and $b_1<\dots<b_k$, and $\eta(a_i) = b_i$,

$$\det L(G)[\bar B, \bar A] = (-1)^{N - k + \sum_{a\in A} a + \sum_{b \in B} b} \sum_{F \in \Phi_{B\to A}(G)} \operatorname{sgn}(\chi_F \circ \eta)\, w(F),$$

where $L(G)[\bar B, \bar A]$ deletes the rows in $B$ and columns in $A$, and $\chi_F : B \to A$ sends each
$b$ to the root it leads to in $F$. With $A = \{i\}$, $B = \{j\}$ this is the classical Matrix-Tree
theorem.

**Proposition 2.** Let $\emptyset \ne A \subsetneq V(G)$ with $\#A = k$, and let $\theta_{\bar A}$ list
$\bar A$ increasingly. Then $L(G)[\bar A, \bar A]$ is invertible if and only if $\Phi_A(G) \ne \emptyset$,
and in that case, for $i, j \in \{1, \dots, N-k\}$,

$$\big(L(G)[\bar A, \bar A]^{-1}\big)_{ij} = -\,\frac{w\big(\Phi_{A \cup \{\theta_{\bar A}(j)\} \to A \cup \{\theta_{\bar A}(i)\}}(G)\big)}{w\big(\Phi_A(G)\big)}.$$

The denominator is nonzero precisely when every terminal strongly connected component of $G$ meets
$A$; the number of roots of any spanning forest is at least the number of terminal components.

## Expansion

Setting $A = B$ in the All-Minors theorem gives $\det L(G)[\bar A, \bar A] = (-1)^{N-k}
w(\Phi_A(G))$, so invertibility is equivalent to the existence of a spanning forest rooted at $A$. The
inverse then follows from Cramer's rule: each adjugate entry is a minor obtained by deleting one more
row and column, which the All-Minors theorem expresses through forests rooted at $A$ plus one extra
root, with a path from the deleted column vertex to it; for $A = \{N-k+1,\dots,N\}$ all permutation
signs cancel, and a relabelling argument handles general $A$. The minors of a Laplacian thus show
massive sign cancellation, and entries of the inverse become manifestly signed rational functions of
the rates. A companion bijection (adding an edge $j \to z$ into a root $z$) gives
$\sum_{j \in V_{\mathrm{in}}(z)\setminus A} w(\Phi_{A\cup\{i\}\to A\cup\{j\}}(G))\,\ell(j\to z) =
w(\Phi_{(A\setminus\{z\})\cup\{i\}\to A}(G))$ for $i \notin A$, $z \in A$.

## Sources

- K.-M. Nam, J. Gunawardena, "Algebraic formulas for first-passage times of Markov processes in the linear framework", Bulletin of Mathematical Biology 87(11) (2025) 161, <https://doi.org/10.1007/s11538-025-01524-z> (PMC12521310). Theorem 1 (All-Minors Matrix-Tree theorem, Eq. 7), Proposition 2, Lemma 3 and Eq. (24).
