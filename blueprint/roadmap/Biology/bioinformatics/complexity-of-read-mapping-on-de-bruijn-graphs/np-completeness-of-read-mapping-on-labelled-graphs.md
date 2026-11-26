# NP-completeness of read mapping on labelled graphs

**Fixed length asymmetric travelling salesman problem (FLATSP).** Given an integer $l$, a directed graph $G = (V, A, c)$ with edge costs $c : A \to \mathbb{N}$, and a threshold $t \in \mathbb{N}$, decide whether $G$ has a path (no repeated node) $p = (v_1, \dots, v_l)$ with $l$ nodes and cost $c(p) = \sum_{j=1}^{l-1} c((v_j, v_{j+1})) \le t$.

**Proposition 1.** FLATSP is NP-complete, even when restricted to unit costs and instances with $l = |V| = t$.

**Graph read mapping problem (GRMP).** Given a directed graph $G = (V, A, x)$ whose edges carry symbols $x : A \to \Sigma$, a word $q = q_1 \cdots q_{|q|} \in \Sigma^*$, a cost function $F : \Sigma \times \Sigma \to \mathbb{N}$ and a threshold $t$, decide whether there is a path $p = (v_1, \dots, v_{|q|+1})$ of $G$ with $|q| + 1$ nodes whose generated word $m$, with $m_i = x((v_i, v_{i+1}))$, satisfies

$$\sum_{i=1}^{|q|} F(m_i, q_i) \le t.$$

**Proposition 2.** GRMP is NP-complete.

## Expansion

Proposition 1 is a reduction from the Hamiltonian path problem: with unit costs and $l = t = |V|$, a path with $|V|$ nodes exists exactly when $G$ has a Hamiltonian path. For Proposition 2, take a FLATSP instance and an alphabet $\{y_0, y_1, \dots\}$ large enough to encode every edge cost, label each edge $e$ by $y_{c(e)}$, let the query be $q = \alpha^{l-1}$ for a fresh letter $\alpha$, and set $F(y_i, \alpha) = i$. Then the mapping cost of a path equals its FLATSP cost, so the two instances have the same answer. Membership in NP is immediate since a candidate path can be checked in linear time.

## Sources

- A. Limasset, B. Cazaux, E. Rivals, P. Peterlongo, "Read mapping on de Bruijn graphs", BMC Bioinformatics 17 (2016) 237, Definitions 1-7, Propositions 1-2 and Theorem 1, <https://doi.org/10.1186/s12859-016-1103-9> (PMC4910249).
