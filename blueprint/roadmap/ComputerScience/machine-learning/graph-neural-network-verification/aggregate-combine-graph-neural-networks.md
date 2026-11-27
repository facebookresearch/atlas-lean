# Aggregate-combine graph neural networks

An aggregate-combine graph neural network computes, layer by layer, a rational feature vector at every vertex of a vertex-colored directed graph from the vertex's own features, sums over its out- and in-neighbors, and a sum over all vertices (global readout). It accepts a vertex when the first final feature is at least one half.

**Definition (Benedikt, Lu and Tan).** An *$n$-graph* is $\mathcal{G} = (V, E, (U_c)_{c \le n})$ with a nonempty finite vertex set $V$, edges $E \subseteq V \times V$ (self-loops allowed) and vertex colors $U_c \subseteq V$; it is *undirected* if $E$ is symmetric. An *$n$-GNN* with $L \ge 1$ layers consists of dimensions $d_0 = n, d_1, \dots, d_L$, computable activation functions $\sigma_\ell : \mathbb{Q} \to \mathbb{Q}$, rational matrices $C_\ell, A_{\ell,\mathrm{out}}, A_{\ell,\mathrm{in}}, R_\ell \in \mathbb{Q}^{d_\ell \times d_{\ell-1}}$ and bias vectors $b_\ell \in \mathbb{Q}^{d_\ell}$. On an $n$-graph, $\xi^{(0)}(v)$ is the $0/1$ indicator vector of the colors of $v$, and for $1 \le \ell \le L$

$$
\xi^{(\ell)}(v) = \sigma_\ell\Bigl(C_\ell\, \xi^{(\ell-1)}(v) + A_{\ell,\mathrm{out}} \sum_{(v,u) \in E} \xi^{(\ell-1)}(u) + A_{\ell,\mathrm{in}} \sum_{(u,v) \in E} \xi^{(\ell-1)}(u) + R_\ell \sum_{u \in V} \xi^{(\ell-1)}(u) + b_\ell\Bigr),
$$

with $\sigma_\ell$ applied entrywise. The GNN *accepts* $(\mathcal{G}, v)$ if the first entry of $\xi^{(L)}(v)$ is at least $1/2$. It is *local* if every $R_\ell$ is zero (no global readout) and *outgoing-only* if every $A_{\ell,\mathrm{in}}$ is zero. Activation functions of interest are the *truncated ReLU* $x \mapsto \min(\max(x, 0), 1)$, which is eventually constant, and the unbounded *ReLU* $x \mapsto \max(x, 0)$.

A GNN is *satisfiable* if it accepts $(\mathcal{G}, v)$ for some graph $\mathcal{G}$ and vertex $v$, and *universally satisfiable* if for some graph it accepts every vertex.

## Depends on

None.

## Proof depends on

None.

## Expansion

Traditional GNNs act on undirected graphs with one neighbor aggregation per layer; the directed version separates out- and in-neighbors. The sum over all vertices is the global readout. Satisfiability is the basic verification question, asking whether some input makes the classifier answer yes; universal satisfiability adds a quantifier alternation.

## Sources

- Michael Benedikt, Chia-Hsuan Lu and Tony Tan, "Decidability of Graph Neural Networks via Logical Characterizations", 51st International Colloquium on Automata, Languages, and Programming (ICALP 2024), LIPIcs 297, Article 127, 2024, <https://doi.org/10.4230/LIPIcs.ICALP.2024.127>, and ACM Transactions on Computational Logic 27(2):1–65, 2026, <https://doi.org/10.1145/3800944>; Section 3 (graphs, GNNs, flavors, acceptance, satisfiability) of arXiv:2404.18151v4, <https://arxiv.org/abs/2404.18151v4>.
