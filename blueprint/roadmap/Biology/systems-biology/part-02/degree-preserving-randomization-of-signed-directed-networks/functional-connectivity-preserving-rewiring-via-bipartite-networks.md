# Functional-connectivity-preserving rewiring via bipartite networks

A **directed signed network** (DSN) $G = (V, E)$ has edges written as triples $(a, b, \ast)$ with source $a$, target $b$ and sign $\ast \in \{+, -\}$; the sign map is $\lambda(a, b, \ast) = \ast$. The edges $(a, b, +)$ and $(a, b, -)$ are distinct and may coexist, but no other parallel edges occur. For $v \in V$ the positive and negative in- and out-stars are

$$I^{\pm}(v) = \{(a, v, \pm) \in E\}, \qquad O^{\pm}(v) = \{(v, b, \pm) \in E\},$$

and the four **signed degrees** $|I^+(v)|, |I^-(v)|, |O^+(v)|, |O^-(v)|$ give the functional characterization of $v$ in a pathway: activated, inhibited, activator, inhibitor. An **F-rewiring** of $G$ is a DSN on the same nodes, with the same number of edges and a different edge set, in which every node keeps all four signed degrees.

Define $f(G) = (B^+, B^-)$, where for $\ast \in \{+, -\}$ the bipartite network $B^\ast = (S^\ast, D^\ast, E^\ast)$ has

$$S^\ast = \{v : \exists (v, x, \ast) \in E\}, \quad D^\ast = \{v : \exists (x, v, \ast) \in E\}, \quad E^\ast = \{(s, d) : (s, d, \ast) \in E\},$$

with a node occurring in both $S^\ast$ and $D^\ast$ relabelled to keep the two sides apart. The map $f$ is a bijection between DSNs and pairs of bipartite networks, with inverse $f^{-1}(B_1, B_2) = (S_1 \cup S_2 \cup D_1 \cup D_2,\ \{(s, d, +) : (s,d) \in E_1\} \cup \{(s, d, -) : (s,d) \in E_2\})$ after undoing the relabelling.

A **rewiring** of a bipartite network keeps both node sets and every node degree and changes the edge set. The **switching algorithm** rewires $B = (S, D, E)$ by repeated switching steps: pick two edges $(a, b), (c, d) \in E$ at random and replace them by $(a, d), (c, b)$ if neither is already in $E$ (a successful step). The successful steps form a Markov chain on bipartite networks with the degrees of $B$, which, run long enough, samples them uniformly.

**Proposition (reduction).** If $R^+$ and $R^-$ are rewirings of $B^+$ and $B^-$, where $f(G) = (B^+, B^-)$, then $f^{-1}(R^+, R^-)$ is an F-rewiring of $G$.

So randomizing a signed pathway while preserving every entity's functional characterization amounts to running the switching algorithm independently on the positive-edge and negative-edge bipartite graphs.

## Expansion

Rewiring leaves node sets unchanged, so $f^{-1}(R^+, R^-)$ has node set $S^+ \cup D^+ \cup S^- \cup D^- = V$. Each $R^\ast$ has $|E^\ast|$ edges and at least one edge not in $E^\ast$, so the result has $|E^+| + |E^-| = |E|$ edges and differs from $E$. The positive out-degree of $v$ in the result is the degree of $v$ as a source node in $R^+$, which equals its degree in $B^+$, which is $|O^+(v)|$ in $G$; the other three signed degrees follow in the same way from the target side of $R^+$ and both sides of $R^-$.

## Sources

- F. Iorio, M. Bernardo-Faura, A. Gobbi, T. Cokelaer, G. Jurman and J. Saez-Rodriguez, "Efficient randomization of biological networks while preserving functional characterization of individual nodes", BMC Bioinformatics 17 (2016), 542, Methods (Preliminary notations; reduction proof, Proposition 1; switching algorithm), <https://doi.org/10.1186/s12859-016-1402-1> (PMC5168876).
