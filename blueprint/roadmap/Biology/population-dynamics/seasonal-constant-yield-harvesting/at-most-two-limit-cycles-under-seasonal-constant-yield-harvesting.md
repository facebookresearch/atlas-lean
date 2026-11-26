# At most two limit cycles under seasonal constant-yield harvesting

**Model.** A single species with density $x \ge 0$ grows at rate $g(x)$ and is harvested at a constant yield $h > 0$ only during the open season of each period $T$:

$$\frac{dx}{dt} = \begin{cases} g(x), & t \in [kT, kT+T_1),\\ g(x) - h, & t \in [kT+T_1, (k+1)T),\end{cases}\qquad 0 < T_1 < T,\ k \in \mathbb{Z}.$$

**Hypothesis (H).** $g \in C^1(\mathbb{R})$ and there are $0 < k_0 < K$ with $g(0) = g(K) = g'(k_0) = 0$, $g' > 0$ on $[0,k_0)$ and $g' < 0$ on $(k_0,\infty)$ (logistic-type growth with maximum $h^* = g(k_0)$). Periodic solutions of period $T$ are limit cycles of the time-periodic equation.

**Theorem.** Under (H), the equation has at most two limit cycles counted with multiplicity. Moreover there is a threshold (the maximum sustainable yield)

$$h_{\mathrm{MSY}} \in \Big(h^*,\ \frac{T}{T-T_1}\,h^*\Big)$$

such that
1. for $0 < h < h_{\mathrm{MSY}}$ there are exactly two limit cycles, the lower unstable and the upper stable;
2. for $h = h_{\mathrm{MSY}}$ there is a unique, semi-stable limit cycle;
3. for $h > h_{\mathrm{MSY}}$ there are no limit cycles.

No concavity of $g$ (such as $g'' < 0$) is assumed.

## Expansion

After normalizing the period, the equation is piecewise autonomous, $\dot x = f_i(x)$ on the $i$-th subinterval, and its Poincaré map $P$ has the discrete derivative formula $P'(x_0) = \prod_i f_i(x_i)/f_i(x_{i-1})$, where $x_i$ is the state at the end of the $i$-th subinterval, with an analogous formula for $P''$. For two pieces, a non-constant periodic solution must cross a region where $f_1 + f_2$ changes sign, and if $f_1+f_2$ changes sign exactly once on an interval there is at most one periodic orbit there, which is hyperbolic with the sign of $P'-1$ determined by the crossing. Applied with $f_1 = g$ and $f_2 = g - h$, the region below and above the maximum of $g$ each carry at most one cycle; monotonicity of $P$ in $h$ then yields a saddle-node bifurcation at $h_{\mathrm{MSY}}$. Averaging bounds the threshold: harvest must exceed the maximal growth $h^*$ on average over the open season only, giving the factor $T/(T-T_1)$.

## Sources

- Renhao Tian, Jianfeng Huang, Yulin Zhao, "On the study of the limit cycles for a class of population models with time-varying factors", arXiv:2410.21848 (2024), Theorems 1.1–1.4 and Proposition 4.1, <https://doi.org/10.48550/arXiv.2410.21848>.
