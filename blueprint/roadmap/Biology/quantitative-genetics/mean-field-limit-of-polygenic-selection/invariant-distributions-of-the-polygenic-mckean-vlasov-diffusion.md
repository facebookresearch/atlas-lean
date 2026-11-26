# Invariant distributions of the polygenic McKean–Vlasov diffusion

**Setting.** Let $f$ solve the locus-level McKean–Vlasov diffusion
$$df_t = \bar s(\mathcal L(f_t))\, f_t(1 - f_t)\, dt + \bigl(\theta^{(+)}(1 - f_t) - \theta^{(-)} f_t\bigr) dt + \sqrt{f_t(1 - f_t)}\, dB_t$$
on $[0,1]$, with $\theta^{(\pm)} > 0$ and $\bar s$ Lipschitz on probability measures. For $y \in \mathbb R$ let
$$\Pi_y(dx) = C_y\, x^{2\theta^{(+)} - 1} (1 - x)^{2\theta^{(-)} - 1} e^{2xy}\, dx,$$
the stationary law of the classical Wright–Fisher diffusion with constant selection $y$, and $\chi(y) = \bar s(\Pi_y)$.

**Theorem.**
1. $\chi$ has at least one fixed point, and the invariant distributions of the McKean–Vlasov diffusion are exactly $\{\Pi_{y^*} : \chi(y^*) = y^*\}$. Started from such a $\Pi_{y^*}$, $f$ is a classical Wright–Fisher diffusion with constant selection $\bar s(\Pi_{y^*})$.
2. For symmetric quadratic selection $\bar s(\xi) = -2\kappa \langle \xi, 2\,\mathrm{Id} - 1\rangle$:
   - (stabilizing) if $\kappa \ge 0$, $\chi$ has the unique fixed point $0$, so the invariant law is unique;
   - (disruptive) if $\theta^{(+)} = \theta^{(-)}$ and $\kappa_c = -\frac{4\theta^{(+)} + 1}{2}$, there is $\delta > 0$ such that for $\kappa \in (\kappa_c - \delta, \kappa_c]$, $\chi$ has at least three fixed points, so several stationary trait distributions coexist.

## Depends on

- [McKean–Vlasov limit of a typical locus under strong recombination](mckean-vlasov-limit-of-a-typical-locus.md)

## Expansion

At stationarity the law of $f$ is constant, so the selection coefficient $\bar s(\mathcal L(f))$ is a constant $y$, and the diffusion is the ordinary Wright–Fisher diffusion with selection $y$, whose unique invariant law is the Wright density $\Pi_y$. Self-consistency requires $y = \bar s(\Pi_y)$; continuity of $\chi$ and boundedness of $\bar s$ give a fixed point. For quadratic selection, $\chi(y) = -2\kappa\,\mathbb E_{\Pi_y}[2X - 1]$ is increasing in $y$ when $\kappa < 0$, and the slope of $\chi$ at $0$ equals $1$ exactly at $\kappa_c$, the pitchfork point where two asymmetric equilibria (trait mean shifted up or down) branch off.

## Sources

- P. Courau, A. Lambert, E. Schertzer, "The gene's-eye view of quantitative genetics", arXiv:2502.12831 (2025), Theorem 1.2 and Corollary 2.4, <https://doi.org/10.48550/arXiv.2502.12831>.
