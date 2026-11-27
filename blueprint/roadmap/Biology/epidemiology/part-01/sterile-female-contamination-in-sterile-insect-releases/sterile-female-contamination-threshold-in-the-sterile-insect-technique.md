# Sterile-female contamination threshold in the sterile insect technique

**Model.** In the sterile insect technique (SIT), sterilized males are released at a constant total rate $\Lambda_{\mathrm{tot}}$, of which a fraction $\epsilon_F$ are accidentally released sterile females. Sterile males keep a residual fertility $\varepsilon \in [0,1)$. The wild mosquito population has aquatic stage $A$, males $M$ and fertilized females $F_{W,S}$. With sterile males at their equilibrium level $M_S^* = (1-\epsilon_F)\Lambda_{\mathrm{tot}}/\mu_{M_S}$, the wild dynamics are

$$\dot A = \phi F_{W,S} - (\gamma + \mu_{A,1} + \mu_{A,2}A)A, \qquad \dot M = (1-r)\gamma A - \mu_M M, \qquad \dot F_{W,S} = \frac{M + \varepsilon M_S^*}{M + M_S^*}\, r\gamma A - \mu_S F_{W,S},$$

with basic offspring number $\mathcal N = r\gamma\phi/(\mu_S(\gamma+\mu_{A,1}))$ and $\mathcal Q = \mu_{A,2}\mu_M/((\gamma+\mu_{A,1})(1-r)\gamma)$. Without SIT, if $\mathcal N > 1$ the wild equilibrium has aquatic density $A^* = (\gamma+\mu_{A,1})(\mathcal N - 1)/\mu_{A,2}$. Released sterile females do not reproduce, but they bite humans and can acquire and transmit the virus. Let $\mathcal R_0^2$ be the squared basic reproduction number of the virus with the wild vector at its SIT-free equilibrium.

**Theorem.**

1. (Elimination by sterile males with residual fertility.) Assume $\mathcal N\varepsilon < 1$ and set

$$\Lambda_M^{\mathrm{crit}} = \frac{\mu_{M_S}}{\mathcal Q}\Bigl(\sqrt{\mathcal N(1-\varepsilon)} - \sqrt{1 - \mathcal N\varepsilon}\Bigr)^2 .$$

If $(1-\epsilon_F)\Lambda_{\mathrm{tot}} > \Lambda_M^{\mathrm{crit}}$, the elimination equilibrium of the wild population is globally asymptotically stable. If $(1-\epsilon_F)\Lambda_{\mathrm{tot}} < \Lambda_M^{\mathrm{crit}}$, there are two positive equilibria $E_1 < E_2$ and the system is bistable: the order interval below $E_1$ lies in the basin of elimination and the region above $E_1$ in the basin of $E_2$. If $\mathcal N\varepsilon > 1$, a unique positive wild equilibrium exists for every release rate, so sterile males alone cannot eliminate the population.

2. (Contamination bound.) Suppose $\mathcal N\varepsilon \le 1$ and $(1-\epsilon_F)\Lambda_{\mathrm{tot}} > \Lambda_M^{\mathrm{crit}}$, so the wild vector is eliminated. The reproduction number of the virus carried only by released sterile females is below $1$ if and only if

$$\epsilon_F\,\Lambda_{\mathrm{tot}} < \Lambda_F^{\mathrm{crit}} := \frac{r\gamma A^*}{\mathcal R_0^2} = \frac{r\gamma(\gamma+\mu_{A,1})(\mathcal N - 1)}{\mu_{A,2}\,\mathcal R_0^2}.$$

If $\epsilon_F\Lambda_{\mathrm{tot}} > \Lambda_F^{\mathrm{crit}}$, the system has a wild-insect-free equilibrium at which the virus persists in humans and in the released sterile females alone.

So the admissible contamination fraction is $\epsilon_F < \Lambda_F^{\mathrm{crit}}/\Lambda_{\mathrm{tot}}$, which shrinks as releases grow. A fixed maximal contamination percentage cannot be safe for every release size.

## Expansion

Equilibria with $A \ne 0$ satisfy $\frac{\phi r\gamma}{\mu_S}\frac{M + \varepsilon M_S^*}{M + M_S^*} = \gamma + \mu_{A,1} + \mu_{A,2}A$ with $M = (1-r)\gamma A/\mu_M$. This reduces to a quadratic in $A$ whose discriminant vanishes exactly at $M_S^* = \Lambda_M^{\mathrm{crit}}/\mu_{M_S}$. The system is cooperative, so monotone-systems theory turns the equilibrium structure into the stated basins. At the trivial disease-free equilibrium, the only vectors are sterile females at density $\epsilon_F\Lambda_{\mathrm{tot}}/\mu_S$. The next-generation matrix scales linearly with that density, and comparing it with the wild female density $r\gamma A^*/\mu_S$ that gives $\mathcal R_0^2$ yields the threshold $\Lambda_F^{\mathrm{crit}}$.

## Sources

- Yves Dumont, Valaire Ivric Yatat-Djeumen, "About contamination by sterile females and residual male fertility on the effectiveness of the sterile insect technique", arXiv (2023). Section 2: Theorems 1–6 (SIT-entomological model, threshold $\Lambda_M^{\mathrm{crit}}$); Section 3: Propositions 1–2 and the remarks defining $\Lambda_F^{\mathrm{crit}}$. <https://doi.org/10.48550/arXiv.2310.13591>. Published version: Mathematical Biosciences 370 (2024), article 109165, <https://doi.org/10.1016/j.mbs.2024.109165>; locators above refer to the arXiv version.
