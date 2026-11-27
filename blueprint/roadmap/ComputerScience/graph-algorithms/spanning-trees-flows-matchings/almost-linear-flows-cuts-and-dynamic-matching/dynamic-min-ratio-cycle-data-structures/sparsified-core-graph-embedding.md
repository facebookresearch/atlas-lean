# Sparsified core graphs with short low-congestion embeddings

For graphs $G, H$ with $V(G) \subseteq V(H)$, an embedding $\Pi_{G \to H}$ maps each edge $(u, v)$ of $G$ to a $u$-$v$ path in $H$; its length is the maximum number of edges of an image path, and its edge congestion is the maximum over $e^H$ of the number of edges of $G$ whose image uses $e^H$. Given a core graph $\mathcal{C}(G, F)$ and parameters $\gamma_\ell, \gamma_c \ge 1$ and $k$, a $(\gamma_\ell, \gamma_c)$-sparsified core graph is a subgraph $\mathcal{S}(G, F) \subseteq \mathcal{C}(G, F)$ with an embedding $\Pi = \Pi_{\mathcal{C}(G,F) \to \mathcal{S}(G,F)}$ such that

1. every edge $\hat{e}'$ on the path $\Pi(\hat{e})$ has $\boldsymbol{\ell}^{\mathcal{C}}_{\hat{e}'} \approx_2 \boldsymbol{\ell}^{\mathcal{C}}_{\hat{e}}$;
2. $\Pi$ has length at most $\gamma_\ell$ and edge congestion at most $k\gamma_c$;
3. $\mathcal{S}(G, F)$ has at most $m\gamma_\ell/k$ edges;
4. edges of $\mathcal{S}(G, F)$ keep their core-graph lengths and gradients.

## Depends on

- [Core graph of a low-stretch forest with stretched lengths and tree-shifted gradients](core-graph-of-low-stretch-forest.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
