# Explosion threshold for degree-penalised transmission on scale-free spatial graphs

**Model.** Vertices of an infinite spatial random graph sit either on $\mathbb{Z}^d$ (scale-free percolation, SFP) or at the points of a homogeneous Poisson process on $\mathbb{R}^d$ (infinite geometric inhomogeneous random graph, IGIRG). Each vertex $v$ carries an i.i.d. weight $W_v \ge 1$ (its expected degree up to constants) with power-law tail of exponent $\tau$, i.e. $\mathbb{P}(W \ge x) = \ell(x)x^{-(\tau-1)}$ with $\ell$ slowly varying. Given positions and weights, $u$ and $v$ are joined independently with probability $h(u-v, W_u, W_v)$, where for a long-range parameter $\alpha \in (0,\infty]$

$$\underline{c}\Big(\ell'(w_1)\ell'(w_2) \wedge \big(w_1w_2/\|x\|^d\big)^\alpha\Big) \le h(x, w_1, w_2) \le \overline{c}\Big(1 \wedge \big(w_1w_2/\|x\|^d\big)^\alpha\Big)$$

with $\ell'(w) = \exp(-c_2(\log w)^\gamma)$, $\gamma \in (0,1)$ (an indicator of $w_1w_2 \gtrsim \|x\|^d$ replaces the power when $\alpha = \infty$). An infection crossing the directed edge $(u,v)$ takes time

$$C_{(u,v)} = L_e\, f(W_u, W_v),$$

with $L_e$ i.i.d. copies of a random variable $L \ge 0$ and a penalty function $f$ that slows transmission through hubs (hubs cannot scale their contacts per unit time). The explosion time $Y_f(0)$ of the origin is the infimum of times $t$ at which infinitely many vertices are reachable from $0$ within total cost $t$; the graph is $(f,L)$-explosive if $\mathbb{P}(Y_f(0) < \infty) > 0$ and $(f,L)$-conservative otherwise. Set

$$\beta^+ = \limsup_{t \to 0}\frac{\log F_L(t)}{\log t}, \qquad \beta^- = \liminf_{t \to 0}\frac{\log F_L(t)}{\log t}.$$

**Theorem (product penalty).** Let $\tau \in (1,3)$ and $f(w_1, w_2) = (w_1w_2)^\mu$ with $\mu > 0$. For both IGIRG and SFP:
1. if $\alpha \le 1$, the graph is sideways explosive (some vertex has infinitely many incident edges of bounded cost) and explosion occurs almost surely;
2. if $\alpha > 1$ and $\beta^+ < (3-\tau)/(2\mu)$, the graph is lengthwise explosive (there is an infinite path of finite cost);
3. if $\alpha > 1$ and $\beta^- > (3-\tau)/(2\mu)$, the graph is conservative.

**Theorem (polynomial penalties).** Let $f(w_1, w_2) = \sum_{i \in \mathcal{I}} a_i w_1^{\mu_i}w_2^{\nu_i}$ with $a_i > 0$, $\mu_i, \nu_i \ge 0$, and $\deg f = \max_i(\mu_i + \nu_i)$. Then: (i) if $\alpha \le 1$, or $\beta^+ < (2-\tau)/\nu_i$ for all $i$, explosion occurs almost surely; (ii) if $\alpha > 1$ and $\beta^+ < (3-\tau)/\deg f$, the graph is lengthwise explosive; (iii) if $\alpha > 1$, $\beta^- > (3-\tau)/\deg f$, and $\beta^- > (2-\tau)/\nu_i$ for some $i$ with $\mu_i + \nu_i = \deg f$, the graph is conservative. For monomials $w_1^\mu w_2^\nu$ this is a full phase transition at $\beta_c = \max\{(3-\tau)/(\mu+\nu), (2-\tau)/\nu\}$, and for $\tau \in (2,3)$ the threshold is $(3-\tau)/\deg f$ for every polynomial penalty.

## Expansion

Without a penalty ($\mu = 0$), first passage percolation on these graphs explodes for essentially every edge-time law with support starting at $0$, which overstates how fast diseases spread on physical contact networks. With the penalty, explosion is governed by a race between hub weights and penalised edge costs. In the explosive regime one builds doubly-exponentially growing annuli around the source, each holding doubly-exponentially many "leader" vertices of doubly-exponential weight; a greedy path jumps between leaders, and the cost of a jump between weights $w$ and $w'$ is about $(ww')^\mu$ times the minimum of many independent $L$'s, which is summable exactly when $\mu\beta < (3-\tau)/2$. For conservativeness one rules out sideways explosion (finitely many cheap edges per vertex) and shows that lengthwise explosion, if possible at all, would happen arbitrarily fast, which a path-counting bound excludes. Asymmetric penalties can produce outward but not inward explosion, a phenomenon possible only for $\tau \le 2$.

## Sources

- Júlia Komjáthy, John Lapinskas, Johannes Lengler, "Stopping explosion by penalising transmission to hubs in scale-free spatial random graphs", arXiv:2004.01149 (2020): Definitions 3.1, 3.2, 3.4, 3.5; Assumption 3.3; Theorem 3.6 (product penalty); Theorem 3.7 (polynomial penalties); Theorem 1.1 (IGIRG special case). <https://doi.org/10.48550/arXiv.2004.01149>
