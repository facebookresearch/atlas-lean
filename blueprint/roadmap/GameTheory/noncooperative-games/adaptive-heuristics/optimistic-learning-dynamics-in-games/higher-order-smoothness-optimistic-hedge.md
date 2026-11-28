# Higher-order smoothness of Optimistic Hedge iterates

For a sequence $z = (z^t)_{t \ge 1}$ in a normed space, define the finite difference $(\Delta z)^t = z^{t+1} - z^t$ and $\Delta^h = \Delta \circ \Delta^{h - 1}$. If all players of a finite game with losses in $[0, 1]$ run Optimistic Hedge for $T$ rounds with $H = \log T$ and step size $\eta \le c/(m (H + 3))$ for a sufficiently small absolute constant $c > 0$, then for every player $i$, every $0 \le h \le H$ and every $t \le T - h$, the loss vectors satisfy

$$
\bigl\lVert (\Delta^h \ell_i)^t \bigr\rVert_\infty \le O(m\eta)^{h}\, h^{O(h)} \quad \text{for all } t,
$$

so loss sequences in Optimistic Hedge dynamics vary like analytic functions of time on a scale of $1/(m\eta)$.

## Proof sketch

Write each player's strategy as a softmax-type function of $\eta$ times sums of its past loss vectors, so that player $i$'s loss vector is a product of such functions of the other players' losses. A boundedness chain rule for finite differences, proved from the Taylor expansion of softmax-type functions (whose radius of convergence at the origin is at least $1$), bounds the order-$h$ finite differences of such a composition in terms of the lower-order finite differences of its argument. Inducting upwards on $h$, jointly over all players, gives the stated bound, with one factor $O(m \eta)$ per order.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Sources

- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924, Lemmas 4.4 and 4.5, Claim B.9.
