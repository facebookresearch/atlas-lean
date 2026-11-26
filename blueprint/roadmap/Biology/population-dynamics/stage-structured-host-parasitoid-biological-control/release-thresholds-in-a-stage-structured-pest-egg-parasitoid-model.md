# Release thresholds in a stage-structured pest–egg-parasitoid model

**Model.** A holometabolous pest with eggs $E$, larvae $Q$, pupae $P$ and adults $A$ is attacked by an egg parasitoid $L$:

$$\begin{aligned}
\dot E &= bA - (\alpha_1 + \mu_1)E - \beta E L, & \dot Q &= \alpha_1 E - (\alpha_2 + \mu_2) Q - \eta Q^2,\\
\dot P &= \alpha_2 Q - (\alpha_3 + \mu_3) P, & \dot A &= \alpha_3 P - \mu_4 A,\\
\dot L &= c\beta E L - (\mu_L + \omega) L + u(t),
\end{aligned}$$

with maturation rates $\alpha_i$, mortalities $\mu_i$, larval competition $\eta$, parasitism rate $\beta$, conversion $c$ and release term $u(t) \ge 0$.

**Theorem.**
1. Solutions are nonnegative and ultimately bounded.
2. *(No release, $u \equiv 0$.)* With $E_0$ the pest egg density at the parasitoid-free equilibrium, $\mathcal R_0 = c\beta E_0/(\mu_L + \omega)$. The parasitoid-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$; when $\mathcal R_0 > 1$ the unique coexistence equilibrium is globally asymptotically stable in the open orthant.
3. *(Continuous release, $u \equiv C > 0$.)* The unique positive equilibrium $E^*_C$ is globally asymptotically stable, and the equilibrium pest densities $E^*_C, Q^*_C, P^*_C, A^*_C$ are strictly decreasing in $C$.
4. *(Impulsive release of $\delta$ parasitoids every $T$ time units.)* The pest-free solution has parasitoid component $\tilde L(t) = \delta e^{-(\mu_L + \omega)(t - nT)}/(1 - e^{-(\mu_L + \omega) T})$ on $(nT, (n+1)T]$, with mean $\langle L \rangle = \delta/((\mu_L + \omega) T)$. Let

$$\mathcal R_{\mathrm{imp}} = \frac{b\,\alpha_1 \alpha_2 \alpha_3}{\mu_4 (\alpha_3 + \mu_3)(\alpha_2 + \mu_2)(\alpha_1 + \mu_1 + \beta \langle L \rangle)} .$$

If $\mathcal R_{\mathrm{imp}} < 1$ the pest-extinction periodic solution $(0,0,0,0,\tilde L)$ is globally asymptotically stable; if $\mathcal R_{\mathrm{imp}} > 1$ the system is permanent (all pest stages stay above some $\epsilon^* > 0$).

## Expansion

$\mathcal R_{\mathrm{imp}}$ is the pest's net reproductive number along the egg–larva–pupa–adult chain, $b/\mu_4$ times the stage survival fractions $\alpha_i/(\alpha_i + \mu_i)$, with the egg loss rate augmented by the average parasitism pressure $\beta\langle L \rangle$ imposed by releases. Linearising the pest equations around the periodic pest-free solution gives a cooperative linear periodic system whose Floquet multiplier is governed by this averaged rate; comparison arguments give global stability, and persistence theory gives permanence. Calibrated to field data, the analysis yields an optimal constant release rate and a release interval of a few days.

## Sources

- W. Li, X. Chen, Y. Gao, S. Liu, "A data-driven stage-structured host-parasitoid model for optimizing Trichogramma interventions against soybean pod borer", arXiv:2607.28053 (2026), Theorems 1, 2, 4, 6, 9, 10, 12 and 13, <https://doi.org/10.48550/arXiv.2607.28053>.
