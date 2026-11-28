# Global stability of the SEIR model with saturated incidence and education

Let $S, E, I_u, I_e, R \ge 0$ be susceptible, exposed, uneducated infected, educated (counselled) infected and recovered individuals, with recruitment $\Pi > 0$, natural death $\mu > 0$, progression rate $\kappa$, education rate $\sigma$, recovery rates $\gamma_1, \gamma_2$, disease-induced death rates $\delta_1, \delta_2$, transmission rate $\beta$, saturation constants $\alpha_1, \alpha_2 \ge 0$ and relative infectiousness $\eta \in [0,1)$ of educated infected. The Holling type II force of infection is

$$\lambda = \beta\Big(\frac{I_u}{1 + \alpha_1 I_u} + \frac{\eta I_e}{1 + \alpha_2 I_e}\Big),$$

and

$$\dot S = \Pi - (\mu + \lambda)S, \quad \dot E = \lambda S - k_1 E, \quad \dot I_u = \kappa E - k_2 I_u, \quad \dot I_e = \sigma I_u - k_3 I_e, \quad \dot R = \gamma_1 I_u + \gamma_2 I_e - \mu R,$$

with $k_1 = \mu + \kappa$, $k_2 = \mu + \sigma + \gamma_1 + \delta_1$, $k_3 = \mu + \gamma_2 + \delta_2$, on the positively invariant region $\mathcal D = \{S + E + I_u + I_e + R \le \Pi/\mu\}$. The disease-free equilibrium is $\mathcal E_0 = (\Pi/\mu, 0,0,0,0)$ and

$$\mathcal R_0 = \frac{\beta \Pi \kappa (k_3 + \eta\sigma)}{\mu k_1 k_2 k_3}.$$

**Theorem.**
1. $\mathcal E_0$ is globally asymptotically stable in $\mathcal D$ whenever $\mathcal R_0 \le 1$.
2. The system is uniformly persistent in the interior of $\mathcal D$ if and only if $\mathcal R_0 > 1$, and then has at least one endemic equilibrium.
3. If educated infected do not transmit ($\eta = 0$), then $\mathcal R_0^r = \beta\Pi\kappa/(\mu k_1 k_2)$ and for $\mathcal R_0^r > 1$ the endemic equilibrium is unique and globally asymptotically stable in the interior of $\mathcal D$.

## Proof depends on

- [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

For part 1, saturation only lowers the incidence: $\lambda S \le \beta(\Pi/\mu)(I_u + \eta I_e)$ on $\mathcal D$. The linear function

$$\mathcal F = \frac{\kappa(k_3 + \eta\sigma)}{\eta k_1 k_2}E + \frac{k_3 + \eta\sigma}{\eta k_2} I_u + I_e$$

then satisfies $\dot{\mathcal F} \le \frac{k_3}{\eta}(\mathcal R_0 - 1)(I_u + \eta I_e) \le 0$, with equality only when the infected classes vanish, and LaSalle's invariance principle gives convergence to $\mathcal E_0$. Part 2 follows from instability of $\mathcal E_0$ for $\mathcal R_0 > 1$ and a uniform persistence theorem, which also yields an interior equilibrium. For part 3, write $f(I) = I/(1 + \alpha_1 I)$ and use the Volterra-type function

$$\mathcal F = S - S^{**}\ln S + E - E^{**}\ln E + \frac{k_1}{\kappa}\big(I_u - I_u^{**}\ln I_u\big).$$

After substituting the equilibrium relations, $\dot{\mathcal F}$ splits into $\mu S^{**}(2 - S^{**}/S - S/S^{**}) \le 0$, a cyclic term $\beta S^{**}f(I_u^{**})\,(4 - \cdots)$ that is non-positive by the arithmetic–geometric mean inequality, and a remainder that is non-positive because $f$ is increasing and $f(I)/I$ is non-increasing (concave incidence). The educated class $I_e$ is downstream and does not feed back when $\eta = 0$, so it converges once $I_u$ does.

## Sources

- M. A. Safi, S. M. Garba, "Global stability analysis of SEIR model with Holling type II incidence function", Computational and Mathematical Methods in Medicine 2012 (2012) 826052, model (8), Theorem 1, Lemma 3, Theorem 4 (Eqs. (19)–(20)), Theorem 5, Lemma 6, Theorem 7 (Eqs. (30)–(37)), <https://doi.org/10.1155/2012/826052>, PMCID PMC3474276.
