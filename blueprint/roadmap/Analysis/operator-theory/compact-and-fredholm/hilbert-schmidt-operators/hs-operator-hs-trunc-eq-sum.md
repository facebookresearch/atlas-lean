# Truncated Hilbert–Schmidt operator as a sum of rank-one operators

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $(e_k)_{k \in \mathbb{N}}$ be the standard basis vectors of $\ell^2(\mathbb{N}, \mathbb{K})$. For every infinite matrix $a = (a_{ij})$ with entries in $\mathbb{K}$ and every $N \in \mathbb{N}$, the [Hilbert–Schmidt operator](hs-operator.md) of the [truncation](hs-trunc.md) $a^{(N)}$ is

$$
T_{a^{(N)}} = \sum_{i=0}^{N-1} \sum_{j=0}^{N-1} a_{ij} R_{ij},
$$

where $R_{ij}$ is the rank-one operator $z \mapsto \langle e_j, z \rangle e_i$.
