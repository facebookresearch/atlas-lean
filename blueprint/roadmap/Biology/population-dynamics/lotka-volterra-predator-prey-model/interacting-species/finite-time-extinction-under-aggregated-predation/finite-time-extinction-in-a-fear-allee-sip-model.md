# Finite-time extinction of prey in a fear–Allee SIP model with sublinear predation

**Model.** Susceptible prey $S$, infectious prey $I$ and predators $P$ satisfy

$$\begin{aligned}
\dot S &= \frac{b_0 S}{1 + k_1 P}\Bigl(1 - \frac{S + I}{K}\Bigr)(S - L) - d_0 S^r P - \frac{e_0 S I}{1 + k_2 P},\\
\dot I &= \frac{e_0 S I}{1 + k_2 P} - d_1 I P - a_1 I,\\
\dot P &= d_2 S^r P + d_3 I P - a_2 P,
\end{aligned}$$

with positive parameters, fear factors $1/(1 + k_i P)$ on prey birth and transmission, an Allee threshold $L$ ($L > 0$ strong, $L < 0$ weak), and aggregation exponent $0 < r < 1$ in the predation term $d_0 S^r P$ (herd defence: only prey on the herd boundary are exposed).

**Theorem.** Solutions with nonnegative data stay nonnegative, and if $d_0 \ge d_2$ and $d_1 \ge d_3$ they are uniformly bounded. Suppose $0 < r < 1$ and on $[0, t_{ext})$

$$0 < S(t) < L, \qquad S(t) + I(t) \le K, \qquad P(t) \ge \underline P > 0 .$$

Then $S$ reaches $0$ in finite time, and

$$t_{ext} \le \frac{S(0)^{1-r}}{(1 - r)\, d_0\, \underline P}.$$

The bound decreases with stronger predator pressure ($\underline P$, $d_0$) and with stronger aggregation (smaller $r$ when $S(0) < 1$). Extinction of $S$ then triggers a cascade collapse of the infectious prey and the predators.

## Expansion

Under the hypotheses the logistic–Allee birth term is nonpositive (since $S < L$ and $S + I \le K$) and the infection term is nonnegative, so $\dot S \le -d_0 \underline P\, S^r$. Comparison with $\dot u = -c u^r$, whose solution $u(t)^{1-r} = u(0)^{1-r} - (1 - r) c t$ hits zero at $t = u(0)^{1-r}/((1-r)c)$, gives the bound. The non-Lipschitz term $S^r$ at $S = 0$ is what permits extinction in finite time; with linear predation ($r = 1$) the decay is only exponential. Aggregation thus protects the herd at high density but accelerates collapse below the Allee threshold.

## Sources

- K. Antwi-Fordjour, E. M. Takyi, "Aggregation as a Double-Edged Sword: Fear, Allee Effects, and Finite-Time Collapse", *Mathematical Biosciences and Engineering* 23(10) (2026), 2998–3036, model (Section 2), Theorems 2.1, 2.2 and 6.2, <https://doi.org/10.3934/mbe.2026104> (preprint arXiv:2606.17586).
