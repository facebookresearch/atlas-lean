# Reproduction number of the HIV–SARS-CoV-2 coinfection model under HAART

**Model.** Healthy target cells $T$, cells infected by HIV only ($I_H$) or SARS-CoV-2 only ($I_S$), coinfected cells $C$, and free virions $V_H, V_S$ satisfy

$$\begin{aligned}
\dot T &= \lambda - k_1(1-\epsilon_{RT})TV_H - k_2TV_S - \mu T,\\
\dot I_H &= k_1(1-\epsilon_{RT})TV_H - k_2I_HV_S - \mu I_H,\\
\dot I_S &= k_2TV_S - k_1(1-\epsilon_{RT})I_SV_H - \mu I_S,\\
\dot V_H &= n_H(1-\epsilon_P)\mu I_H - \sigma_H V_H,\\
\dot V_S &= n_S\mu I_S - \sigma_S V_S,\\
\dot C &= k_1(1-\epsilon_{RT})I_SV_H + k_2I_HV_S - \mu C,
\end{aligned}$$

with all parameters positive. HAART enters through the efficacies $\epsilon_{RT}, \epsilon_P \in [0,1)$ of reverse-transcriptase and protease inhibitors; $k_1,k_2$ are infection rates, $n_H, n_S$ burst sizes, $\sigma_H,\sigma_S$ clearance rates and $\lambda/\mu$ the cell-free target-cell level.

**Theorem.** Solutions starting in $\mathbb R^6_{\ge0}$ stay non-negative and bounded. The single-virus submodels have reproduction numbers

$$\mathcal R_{\mathrm{hiv}} = \frac{k_1 n_H(1-\epsilon_{RT})(1-\epsilon_P)\lambda}{\mu\,\sigma_H}, \qquad \mathcal R_{\mathrm{sars}} = \frac{k_2 n_S\lambda}{\mu\,\sigma_S},$$

and the full model has

$$\mathcal R_0 = \max\{\mathcal R_{\mathrm{hiv}}, \mathcal R_{\mathrm{sars}}\}.$$

The disease-free equilibrium $(\lambda/\mu, 0,0,0,0,0)$ is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$. In each submodel the disease-free equilibrium is stable for reproduction number below $1$; the endemic equilibrium $E^e_{\mathrm{hiv}}$ (respectively $E^e_{\mathrm{sars}}$) enters the positive orthant through a transcritical bifurcation at $\mathcal R_{\mathrm{hiv}} = 1$ (respectively $\mathcal R_{\mathrm{sars}} = 1$) and is locally asymptotically stable above it. Therapy lowers $\mathcal R_{\mathrm{hiv}}$ by the factor $(1-\epsilon_{RT})(1-\epsilon_P)$ and so can clear HIV without affecting the SARS-CoV-2 threshold.

## Proof depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

At the disease-free equilibrium the infected compartments $(I_H, I_S, V_H, V_S, C)$ decouple into an HIV block and a SARS-CoV-2 block, because the coinfection terms $k_2I_HV_S$ and $k_1(1-\epsilon_{RT})I_SV_H$ are quadratic in infected variables and vanish from the linearization. The next-generation matrix $FV^{-1}$ is therefore block-diagonal, and its spectral radius is the larger of the two block radii. For the HIV block, a virion infects $k_1(1-\epsilon_{RT})\lambda/\mu$ cells per unit time during its mean lifetime $1/\sigma_H$, and each infected cell releases $n_H(1-\epsilon_P)$ virions over its lifetime, giving $\mathcal R_{\mathrm{hiv}}$; the SARS-CoV-2 block is analogous. Boundedness follows from adding the cell equations, $\frac{d}{dt}(T + I_H + I_S + C) = \lambda - \mu(T + I_H + I_S + C)$.

## Sources

- João Paulo Simões Maurício de Carvalho, "Qualitative analysis of HAART effects on HIV and SARS-CoV-2 coinfection model", *Applications of Mathematics* 70 (2025), 495–516, <https://doi.org/10.21136/am.2025.0280-24>. Preprint version: arXiv:2411.01374 (2024), model equations, boundedness theorem, submodel reproduction numbers, bifurcation theorem and full-model reproduction number theorem, <https://doi.org/10.48550/arXiv.2411.01374>.
