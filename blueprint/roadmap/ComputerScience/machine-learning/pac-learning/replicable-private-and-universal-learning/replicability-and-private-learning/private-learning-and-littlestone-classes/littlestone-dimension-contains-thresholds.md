# Large Littlestone dimension forces large threshold subclasses

Let $H \subseteq \{0,1\}^X$ have Littlestone dimension at least $d$. Then $H$ contains thresholds of size $\lfloor \log_2 d \rfloor$: there are points $x_1, \dots, x_k \in X$ and concepts $h_1, \dots, h_k \in H$, $k = \lfloor \log_2 d \rfloor$, with $h_i(x_j) = \mathbf{1}[j \ge i]$ for all $i, j$ (or the reversed pattern). Conversely, a class containing thresholds of size $k$ has Littlestone dimension at least $\lfloor \log_2 k \rfloor$. Thus finite Littlestone dimension is equivalent to a uniform bound on the size of embedded thresholds (Shelah's stability theory).

## Proof sketch

Given a Littlestone tree of depth $d$, follow a branch and use a Ramsey-type halving argument: at each step, either the subtree on the left or on the right contains a Littlestone tree of half the depth that is consistent with a threshold pattern relative to the points already chosen, so one obtains $\log_2 d$ points and concepts realizing a threshold order. The converse is binary search over the ordered points, which builds a Littlestone tree of depth $\lfloor \log_2 k \rfloor$.

## Depends on

- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Sources

- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949.
- S. Shelah, "Classification Theory and the Number of Non-Isomorphic Models", North-Holland (1978; revised 1990).
