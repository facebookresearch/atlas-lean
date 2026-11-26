# Non-monotone dependence of the reproduction number on dispersal rates

Take two regions in the multi-patch SIS model with infection during travel. Region $j$ has contact rate $\beta_j$, death rate $d_j$, recovery rate $\delta_j$; individuals move from region $k$ to region $j$ at rate $\alpha_{jk} > 0$ and travel for time $\tau_{jk}$ with in-transit contact and recovery rates $\beta^T_{jk}, \delta^T_{jk}$. Writing

$$R_j = \frac{\beta_j}{d_j + \delta_j + \alpha_{kj}}, \qquad r_{jk} = \frac{\alpha_{jk}\, e^{(\beta^T_{jk} - \delta^T_{jk})\tau_{jk}}}{d_k + \delta_k + \alpha_{jk}} \quad (k \ne j),$$

the basic reproduction number is

$$\mathcal R_0 = \tfrac12\Bigl(R_1 + R_2 + \sqrt{(R_1 - R_2)^2 + 4 r_{12} r_{21}}\Bigr).$$

Let $R_j(0) = \beta_j/(d_j + \delta_j)$ be the local reproduction numbers without travel, assume $R_1(0) \ge R_2(0)$, and define the in-transit reproduction number

$$\eta = \exp\Bigl(\tfrac12\bigl[(\beta^T_{21} - \delta^T_{21})\tau_{21} + (\beta^T_{12} - \delta^T_{12})\tau_{12}\bigr]\Bigr) = \lim_{\alpha_{12}, \alpha_{21} \to \infty} \mathcal R_0 .$$

Write $\partial_1 = \partial/\partial \alpha_{21}$ (travel out of region $1$) and $\partial_2 = \partial/\partial \alpha_{12}$ (travel out of region $2$).

**Theorem.** For $\alpha_{21}, \alpha_{12} > 0$:

1. If $R_1(0) > R_2(0)$:
   - if $\eta > R_1(0)$, there is $z_1 > 0$ with $\partial_1 \mathcal R_0 < 0$ for $\alpha_{12} < z_1$, $= 0$ at $\alpha_{12} = z_1$, $> 0$ for $\alpha_{12} > z_1$, and $\partial_2 \mathcal R_0 > 0$;
   - if $R_1(0) \ge \eta > R_2(0)$ or $R_1(0) > \eta \ge R_2(0)$, then $\partial_1 \mathcal R_0 < 0$ and $\partial_2 \mathcal R_0 > 0$;
   - if $R_2(0) > \eta$, then $\partial_1 \mathcal R_0 < 0$, and there is $z_2 > 0$ with $\partial_2 \mathcal R_0 > 0$ for $\alpha_{21} < z_2$, $= 0$ at $z_2$, $< 0$ for $\alpha_{21} > z_2$.
2. If $R_1(0) = R_2(0)$: both partial derivatives are positive when $\eta > R_1(0)$, both vanish when $\eta = R_1(0)$, and both are negative when $\eta < R_1(0)$.

So reducing travel out of the high-risk region can raise or lower $\mathcal R_0$ depending on the other dispersal rate; with equal local risks, $\mathcal R_0$ is monotone in each dispersal rate and the direction is set by whether travel is riskier than staying home.

## Depends on

- [Endemic patterns on non-strongly-connected transportation networks](endemic-patterns-on-non-strongly-connected-transportation-networks.md)

## Expansion

The formula for $\mathcal R_0$ is the larger root of $(R_1 - \lambda)(R_2 - \lambda) - r_{12} r_{21} = 0$ for the $2 \times 2$ next-generation matrix. As both dispersal rates grow, $R_j \to 0$ and $r_{12} r_{21} \to e^{(\beta^T_{21} - \delta^T_{21})\tau_{21} + (\beta^T_{12} - \delta^T_{12})\tau_{12}}$, so $\mathcal R_0 \to \eta$. Differentiating the characteristic equation implicitly expresses the sign of $\partial_j \mathcal R_0$ through the relative order of $R_1(0)$, $R_2(0)$ and $\eta$. Intuitively, sending infectives from region $1$ to the safer region $2$ dilutes transmission (dilution effect), but if region $2$ empties quickly back into region $1$ or the journey itself is a strong transmission setting, more travel adds infections. The paper's influenza-like example, with $R_1(0) \approx 2.45$, $R_2(0) \approx 0.70$ and $\eta \approx 4.35$, exhibits the first non-monotone case.

## Sources

- Y. Nakata, G. Röst, "Global analysis for spread of infectious diseases via transportation networks", *Journal of Mathematical Biology* (2015), Sections 6–7 (Eqs. (6.3)–(6.4), (7.1), Proposition 6.1, Theorem 7.1, Table 2), <https://doi.org/10.1007/s00285-014-0801-z> (PMC7080142).
