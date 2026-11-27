# City-level isolation strategies in a gravity-kernel inter-city epidemic

**Model.** $N$ cities have i.i.d. sizes with law $\beta$ on $(0,\infty)$; write $\mathcal{Z}_\gamma = \int y^\gamma\,\beta(dy)$. Travel between cities follows a gravity kernel $M_{ij} = k_M x_i^{1+b}x_j^a$ (outbound propensity $x^b$ per inhabitant, attractiveness $x^a$). An infected city of size $x$ accumulates $L(x)$ infected inhabitants before it is isolated, with two strategies: *proportional* (P), $L(x) = p_\vee x$, and *uniform* (U), $L(x) = L_\vee$. City $i$ infects city $j$ (directed edge of the epidemic graph) with probability $1 - \exp[-k_C(M_{ij} + M_{ji})L(x_i)/x_i]$. With $k_B = Nk_Ck_M$ fixed as $N \to \infty$, the outbreak is approximated by a two-type branching process (cities infected by inbound vs outbound travel).

**Infection probabilities.** The probability $\pi(x)$ that a city of size $x$ is reached by a large outbreak solves

$$\pi_P(x) = 1 - \exp\Big[-k_Bp_\vee\Big(x^a\!\int y^{b+1}\pi_P\,d\beta + x^{b+1}\!\int y^a\pi_P\,d\beta\Big)\Big],$$

$$\pi_U(x) = 1 - \exp\Big[-k_BL_\vee\Big(x^a\!\int y^{b}\pi_U\,d\beta + x^{b+1}\!\int y^{a-1}\pi_U\,d\beta\Big)\Big].$$

The expected numbers infected and isolated are $I_P = \int p_\vee x\,\pi_P\,d\beta$, $I_U = \int L_\vee\pi_U\,d\beta$ and $Q_\bullet = \int x\,\pi_\bullet\,d\beta$.

**Proposition (basic reproduction number).** $R_0 = \lim_k \mathbb{E}_x[X_k]^{1/k}$, with $X_k$ the number of cities infected in generation $k$, does not depend on $x$ and equals the dominant eigenvalue of a $2\times 2$ inbound/outbound matrix; explicitly

$$R_0^{(U)} = k_BL_\vee\big(\mathcal{Z}_{a+b} + \sqrt{\mathcal{Z}_{2a-1}\mathcal{Z}_{2b+1}}\big), \qquad R_0^{(P)} = k_Bp_\vee\big(\mathcal{Z}_{1+a+b} + \sqrt{\mathcal{Z}_{2a}\mathcal{Z}_{2b+2}}\big).$$

**Proposition (which strategy isolates fewer people).** Let $\beta$ be non-degenerate, $a = b + 1$, and tune $L_\vee$, $p_\vee$ so that both strategies give the same number of infected people $I_U = I_P = I_\star$. Then: if $a = 1$, $Q_U = Q_P$; if $a < 1$, $Q_U > Q_P$ (proportional isolation is more efficient); if $a > 1$, $Q_U < Q_P$ (uniform isolation is more efficient). Moreover, with $\gamma = 2a \vee (2+2b)$ and $\delta \le (2a-1)\wedge(2b+1)$, if $\mathcal{Z}_\gamma < \infty$ then $\mathcal{Z}_{\delta+1}r_0^U \le \mathcal{Z}_\delta r_0^P$, so at equal $R_0$ one has $p_\vee \le L_\vee\mathcal{Z}_\delta/\mathcal{Z}_{\delta+1}$.

## Proof sketch

The linearised infection operator maps $f$ to a combination of $x^a$ and $x^{b+1}$, so it has rank two and its nonzero spectrum is that of the $2\times2$ matrix of moments; its Perron root gives $R_0$, and $\pi$ is the survival probability of the corresponding backward branching process. When $a = b + 1$ the two powers coincide, the kernel becomes rank one, $\pi_\bullet(x) = 1 - e^{-c_\bullet x^a}$ for a scalar $c_\bullet$ fixed by a one-dimensional equation, and comparing $Q$ at equal $I_\star$ reduces to a Jensen/Chebyshev-type inequality between moments of $\beta$ whose direction flips at $a = 1$. Mobility data (France, Poland, Japan) give estimated exponents $(a,b)$ used to evaluate both strategies.

## Sources

- Viktor Bezborodov, Tyll Krueger, Cornelia Pokalyuk, Piotr Szymański and Aurélien Velleret, "Inter-city infections and the role of size heterogeneity in containment strategies", *Journal of Theoretical Biology* 615 (2025), 112247, <https://doi.org/10.1016/j.jtbi.2025.112247>. Preprint version: arXiv:2402.03100 (2024), Sections 2 and 4 (Propositions 4.3.1, 4.4.1 and 4.5.1, computation of the basic reproduction number), <https://doi.org/10.48550/arXiv.2402.03100>.
