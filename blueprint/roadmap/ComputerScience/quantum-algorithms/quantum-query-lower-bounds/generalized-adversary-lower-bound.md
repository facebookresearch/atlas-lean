# Generalized adversary lower bound

Let $f : D \to \{0,1\}$ with $D \subseteq \{0,1\}^N$. An adversary matrix is a real symmetric matrix $\Gamma$
indexed by $D$ with $\Gamma[x,y] = 0$ whenever $f(x) = f(y)$; for $i \in [N]$ let $D_i[x,y] = 1$ if
$x_i \ne y_i$ and $0$ otherwise. For every nonzero adversary matrix, every quantum query algorithm computing
$f$ with bounded error uses

$$\Omega\Big(\frac{\|\Gamma\|}{\max_i \|\Gamma \circ D_i\|}\Big)$$

queries, where $\circ$ is the entrywise product and $\|\cdot\|$ the operator norm.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Quantum query (oracle) model.
- Proof prerequisite: Adversary output condition.

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §12.1, Theorem 2. <https://arxiv.org/pdf/1907.09415v6>
