# Typical transmission time in finite scale-free spatial graphs with hub penalties

**Model.** A geometric inhomogeneous random graph $\mathrm{GIRG}_{W,L}(n)$ has $n$ vertices placed in a $d$-dimensional torus of volume $n$, i.i.d. power-law weights with exponent $\tau \in (2,3)$, and edges present independently with probability comparable to $1 \wedge (w_uw_v/\|x_u - x_v\|^d)^\alpha$ for some $\alpha > 1$ (or a weight-dependent distance threshold when $\alpha = \infty$); hyperbolic random graphs are a special case. Each edge gets an i.i.d. random time $L_e$, and an infection crossing the directed edge $(u,v)$ takes time $L_e f(W_u, W_v)$ for a polynomial penalty $f(w_1,w_2) = \sum_i a_i w_1^{\mu_i}w_2^{\nu_i}$ of degree $\deg f = \max_i(\mu_i + \nu_i)$. Let $d_{f,L}(u,v)$ be the minimal total transmission time along a path from $u$ to $v$, and $\beta^\pm$ the upper and lower polynomial exponents of $F_L$ at $0$, as in the [explosion threshold](explosion-threshold-for-degree-penalised-transmission.md).

**Theorem (giant component).** Under the edge and weight assumptions above with $2 < \tau < 3$, with high probability $\mathrm{GIRG}_W(n)$ has a unique giant component $\mathcal{C}_{\max}$ of linear size.

**Theorem (cost-distances in GIRG).** Let $v^1_n, v^2_n$ be two uniformly chosen vertices of $\mathcal{C}_{\max}$.
1. If $\beta^+ < (3-\tau)/\deg f$, then $\big(d_{f,L}(v^1_n, v^2_n)\big)_{n \ge 1}$ is tight: the typical transmission time stays bounded as the population grows.
2. If $\beta^- > (3-\tau)/\deg f$, then $d_{f,L}(v^1_n, v^2_n) \to \infty$ in probability.

**Theorem (limit law in the explosive case).** If in addition the connection probabilities and weight laws converge, as $n \to \infty$, to those of an infinite model $\mathrm{IGIRG}_{W,L}(1)$, and $\beta^+ < (3-\tau)/\deg f$, then

$$d_{f,L}(v^1_n, v^2_n) \Rightarrow Y^{(1)} + Y^{(2)},$$

where $Y^{(1)}, Y^{(2)}$ are independent copies of the explosion time of the origin in the infinite model, conditioned to be finite.

## Depends on

- [Explosion threshold for degree-penalised transmission on scale-free spatial graphs](explosion-threshold-for-degree-penalised-transmission.md)

## Expansion

Tightness is the finite-population counterpart of explosion: for any $\varepsilon > 0$ and confidence $p < 1$ there is a constant time, independent of $n$, within which all but an $\varepsilon$-fraction of the giant is infected with probability $p$. The giant component is built bottom-up: a vertex is "successful" if a nearby path leads to a moderately high-weight vertex, boxes with linearly many successful vertices occur independently with positive probability, and their local giants are merged through chains of increasing weight up to the top hubs, whose induced graph dominates an Erdős–Rényi graph. For the limit law, each endpoint first explodes in its own large-but-finite neighborhood of bounded-weight vertices, then the two exploded neighborhoods are joined through hubs at negligible additional cost, so the typical time is the sum of two independent explosion times.

## Sources

- Júlia Komjáthy, John Lapinskas, Johannes Lengler, "Stopping explosion by penalising transmission to hubs in scale-free spatial random graphs", arXiv:2004.01149 (2020): Definition 3.8 and Assumptions 3.9–3.10 (finite GIRG), Theorem 3.11 (giant component), Theorem 3.12 (cost-distances in GIRG), Theorem 3.13 (explosive case limit law), Corollary 3.15 (hyperbolic random graphs). <https://doi.org/10.48550/arXiv.2004.01149>
