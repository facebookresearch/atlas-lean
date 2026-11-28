# A finite digraph is acyclic if and only if it has a topological order

Let $G$ be a digraph on a finite vertex type $V$. Then $G$ is acyclic (no vertex reaches itself by a directed walk of positive length) if and only if there is a bijection $\sigma : V \to \{0, 1, \dots, |V|-1\}$ with $\sigma(u) < \sigma(v)$ for every edge $u \to v$ of $G$.
