# Higher-order smoothness of Optimistic Hedge iterates

For a sequence $z = (z^t)_{t \ge 1}$ in a normed space, define the finite difference $(\Delta z)^t = z^{t+1} - z^t$ and $\Delta^h = \Delta \circ \Delta^{h - 1}$. If all players of a finite game with losses in $[0, 1]$ run Optimistic Hedge with step size $\eta \le c/(m H)$ for a sufficiently small absolute constant $c > 0$ and an integer $H \ge 1$, then for every player $i$ and every $1 \le h \le H$, the loss vectors satisfy

$$
\bigl\lVert (\Delta^h \ell_i)^t \bigr\rVert_\infty \le O(m\eta)^{h}\, h^{O(h)} \quad \text{for all } t,
$$

so loss sequences in Optimistic Hedge dynamics vary like analytic functions of time on a scale of $1/(m\eta)$.

## Proof sketch

Write each player's strategy as a softmax of a linear combination of past loss vectors, and expand finite differences of compositions using a discrete Faà di Bruno formula. Bounding the derivatives of the softmax map in terms of Bell-number-like combinatorial quantities and inducting on $h$ jointly over all players shows that each finite difference of order $h$ is a sum of products of lower-order differences, each carrying a factor $\eta$, which gives the stated factorial-type growth.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Sources

- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924.
