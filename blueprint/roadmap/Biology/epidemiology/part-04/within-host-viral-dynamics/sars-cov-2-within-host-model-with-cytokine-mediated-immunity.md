# SARS-CoV-2 within-host model with cytokine-mediated immunity

**Model.** Healthy target cells $H$, infected cells $I$, virions $V$, cytokines $C$ (interferons), natural killer cells $N$, cytotoxic T cells $T$, B cells $B$ and antibodies $A$ satisfy

$$\begin{aligned}
\dot H &= \Pi - \beta H V - \mu_1 H, & \dot N &= r C - \mu_5 N,\\
\dot I &= \beta H V - p_1 T I - p_5 N I - \mu_2 I, & \dot T &= \lambda_1 C T - \mu_6 T,\\
\dot V &= k_1 I - p_2 C V - p_3 A V - \mu_3 V, & \dot B &= \lambda_2 T B - \mu_7 B,\\
\dot C &= \frac{k_2 I}{1 + \gamma V} - \mu_4 C, & \dot A &= G(t - \tau)\,\eta B - p_4 A V - \mu_8 A,
\end{aligned}$$

where the factor $1/(1 + \gamma V)$ models viral suppression of interferon production (immunosuppression through the JAK/STAT pathway), $G$ is the Heaviside function and $\tau$ the delay before antibody production starts. All parameters are positive.

**Reproduction number.** The disease-free equilibrium is $E_0 = (\Pi/\mu_1, 0, \dots, 0)$ and

$$\mathcal{R}_0 = \frac{\Pi \beta k_1}{\mu_1 \mu_2 \mu_3}.$$

$E_0$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

**Immune-free persistence.** For $\mathcal{R}_0 > 1$ there is an equilibrium without immune activity,

$$E_1:\quad H_1 = \frac{\Pi}{\mu_1\mathcal{R}_0}, \quad I_1 = \frac{\mu_1\mu_3}{\beta k_1}(\mathcal{R}_0 - 1), \quad V_1 = \frac{\mu_1}{\beta}(\mathcal{R}_0 - 1), \quad C = N = T = B = A = 0 .$$

Further equilibria with innate immunity only ($T = B = A = 0$) and with full innate and adaptive responses exist under additional threshold conditions; at the full equilibrium $C^* = \mu_6/\lambda_1$ and $T^* = \mu_7/\lambda_2$, fixed by the T- and B-cell equations.

**Antiviral treatment.** With a drug blocking infection with efficacy $\epsilon_1$ (replacing $\beta$ by $(1-\epsilon_1)\beta$) and one blocking virion production with efficacy $\epsilon_2$ (replacing $k_1$ by $(1-\epsilon_2)k_1$), the control reproduction number is

$$\mathcal{R}_c = (1-\epsilon_1)(1-\epsilon_2)\,\mathcal{R}_0 < \mathcal{R}_0 .$$

## Expansion

At $E_0$ all immune compartments are zero, so the immune equations decouple at linear order and contribute only the eigenvalues $-\mu_4, \dots, -\mu_8$ (the T- and B-cell equations are bilinear in immune variables); the threshold comes from the $(I, V)$ block $\begin{pmatrix} -\mu_2 & \beta\Pi/\mu_1 \\ k_1 & -\mu_3\end{pmatrix}$, whose determinant is $\mu_2\mu_3(1 - \mathcal{R}_0)$. This is the same threshold as in the target-cell model, because the immune response only acts once infection is established. The steady-state values $C^* = \mu_6/\lambda_1$ and $T^* = \mu_7/\lambda_2$ are the levels at which effector proliferation balances death, analogous to $S^* = 1/\mathcal{R}_0$ in epidemic models. In simulations, raising $\epsilon_1$ lowers the viral peak without shortening high viral load, whereas raising $\epsilon_2$ shortens it.

## Depends on

- [Global stability of the target-cell model by the Li–Muldowney criterion](global-stability-of-the-target-cell-model-by-the-li-muldowney-criterion.md)

## Sources

- I. Ghosh, "Within Host Dynamics of SARS-CoV-2 in Humans: Modeling Immune Responses and Antiviral Treatments", SN Computer Science 2 (2021) 482, Sections "Model formulation" (system (1)) and "Equilibria and basic reproduction number" (equilibria $E_0$–$E_3$, Theorem 1, equation (2)), and the antiviral model (6)–(7), <https://doi.org/10.1007/s42979-021-00919-8>.
