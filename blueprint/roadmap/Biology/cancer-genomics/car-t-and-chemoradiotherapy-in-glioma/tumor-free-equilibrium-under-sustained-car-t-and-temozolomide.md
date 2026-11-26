# Tumor-free equilibrium under sustained CAR-T and temozolomide therapy

A glioma is split into three phenotypes, each with a proliferative and a quiescent compartment: fully sensitive $(S,Q)$, CAR-T-resistant but temozolomide-sensitive $(R_C,Q_C)$, and temozolomide-resistant but CAR-T-sensitive $(R_E,Q_E)$; $D$ is lethally damaged tissue, $C$ the active CAR-T effectors and $E$ the effective temozolomide (TMZ) concentration. With total burden $T = S+Q+R_C+Q_C+R_E+Q_E+D$, the continuous-treatment version of the model reads, for the proliferative compartments,

$$\dot S = r_1 S\Big(1-\frac{T}{K}\Big) - \beta_1 S + (\beta_2+\gamma_1)Q - \alpha_4 S - (\alpha_1+\epsilon_1)ES - \alpha_2 CS,$$

$$\dot R_C = r_1 R_C\Big(1-\frac{T}{K}\Big) - \beta_1 R_C + (\beta_2+\gamma_1)Q_C - \alpha_4 R_C - (\alpha_1+\epsilon_1)ER_C,$$

$$\dot R_E = r_2 R_E\Big(1-\frac{T}{K}\Big) - \beta_1 R_E + (\beta_2+\gamma_1)Q_E - \alpha_5 R_E - \alpha_2 CR_E + \epsilon_1(S+R_C)E,$$

with quiescent pools $\dot Q = \beta_1 S - (\beta_2+\gamma_1)Q$ (and likewise for $Q_C, Q_E$), and treatment variables

$$\dot E = \bar E_0 - \mu E, \qquad \dot C = \bar C_0 - (\rho_1+\alpha_6)C - \alpha_3 EC + (\text{tumor-stimulated expansion terms vanishing when } T = 0).$$

Here $\bar E_0, \bar C_0$ are sustained TMZ and CAR-T supply rates, $\alpha_1, \alpha_2$ the TMZ and CAR-T kill rates, $\epsilon_1$ the rate of acquiring TMZ resistance, $\alpha_3$ TMZ lymphotoxicity, and $\alpha_4,\alpha_5,\alpha_6,\gamma_1$ continuous radiotherapy effects (tumor kill, CAR-T loss, recruitment of quiescent cells).

**Proposition.** With constant treatment the system has a tumor-free equilibrium $P = (0,\dots,0,C^*,E^*)$ with

$$E^* = \frac{\bar E_0}{\mu}, \qquad C^* = \frac{\bar C_0}{(\rho_1+\alpha_6) + \alpha_3 \bar E_0/\mu},$$

and $P$ is locally asymptotically stable if and only if

$$(\alpha_1+\epsilon_1)\bar E_0 > \mu\,(r_1 - \alpha_4), \qquad \bar C_0 > \Big((\rho_1+\alpha_6) + \frac{\alpha_3}{\mu}\bar E_0\Big)\frac{r_2-\alpha_5}{\alpha_2}.$$

The first inequality says TMZ must outpace the net growth of the CAR-T-resistant line; the second says CAR-T, after TMZ-induced depletion, must outpace the net growth of the TMZ-resistant line. Without therapy the origin is a saddle, and the hyperplane $T_1 = K$ (with $T_1 = S+Q+R_C+Q_C+R_E+Q_E$) is invariant.

## Expansion

At $P$ the Jacobian is block triangular: the treatment block has eigenvalues $-\mu$ and $-(\rho_1+\alpha_6+\alpha_3E^*)$, and each phenotype contributes a $2\times2$ proliferative–quiescent block with the death terms evaluated at $(C^*,E^*)$. The influx $\epsilon_1(S+R_C)E$ couples phenotypes only one way, so stability reduces to the phenotype blocks. The $R_C$ block is controlled only by TMZ and radiotherapy and the $R_E$ block only by CAR-T and radiotherapy; requiring each net growth rate to be negative gives the two thresholds. The thresholds are theoretical eradication benchmarks for the continuous surrogate of the impulsive clinical schedule, not dosing rules.

## Sources

- Dmitry Sinelshchikov, Nikols Amaru Mora Millán, Miguel Perales-Patón, Juan Belmonte-Beitia, "Combining standard chemoradiotherapy with CAR-T cell therapy in malignant gliomas: insights from an impulsive mathematical framework and virtual trials", arXiv (2026). Section 2 (model), Section 3 (Propositions 2–7) and Appendix A (continuous-treatment system). <https://doi.org/10.48550/arXiv.2609.39191>
