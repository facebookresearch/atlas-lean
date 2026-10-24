---
article_id: af_e3a534e03021319dbc3b6096
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CanonicalPaths.conductance_lower_bound
---

# Lemma 8 (Section 4.2.4 (How to Sample (Approximately) Uniformly), Lecture 5)

Let $G = (V, E)$ be a graph for which we wish to bound $\Phi(G)$. For every $v, w \in V$, we specify a canonical path $p_{v,w}$ from $v$ to $w$. Suppose that for some constant $b$ and for all $e \in E$, we have $\sum_{v,w \in V} \mathbf{I}[e \in p_{v,w}] \leq b|V|$, that is, at most $b|V|$ of the canonical paths run through any given edge $e$. Then $\Phi(G) \geq \frac{1}{4 b d_{\max}}$, where $d_{\max}$ is the maximum degree of any vertex.

## Depends on

- [Definition 7 (Conductance)](../section-6/043-conductance.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Section 4.2.4 (How to Sample (Approximately) Uniformly), Lecture 5](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
