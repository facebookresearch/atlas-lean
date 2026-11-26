# Threshold stability of a Caputo fractional-order malaria model with temporary immunity

**Setting.** Human hosts are split into susceptible, infected and immune proportions $s_h + i_h + r_h = 1$, and mosquitoes into susceptible and infected proportions $s_v + i_v = 1$. With biting rate $a$, human infection probability per bite $b$, mosquito infection probability $c$, mosquito-to-human ratio $m$, human recovery $\nu$, immunity acquisition $r$, loss of immunity $\gamma$, disease-induced death $\delta$, and birth rates $\lambda_h, \lambda_v$, the integer-order model of Tumwiine et al. is replaced by Caputo derivatives $D^\alpha$ of order $0 < \alpha \le 1$, each rate raised to the power $\alpha$ to keep dimensions consistent:

$$D^\alpha s_h = \lambda_h^\alpha(1 - s_h) - a^\alpha b m\, s_h i_v + \nu^\alpha i_h + \gamma^\alpha r_h + \delta^\alpha s_h i_h, \qquad D^\alpha i_h = a^\alpha b m\, s_h i_v - (\nu^\alpha + r^\alpha + \lambda_h^\alpha + \delta^\alpha) i_h + \delta^\alpha i_h^2,$$

$$D^\alpha r_h = r^\alpha i_h - (\gamma^\alpha + \lambda_h^\alpha) r_h + \delta^\alpha i_h r_h, \qquad D^\alpha s_v = \lambda_v^\alpha(1 - s_v) - a^\alpha c\, i_h s_v, \qquad D^\alpha i_v = a^\alpha c\, s_v i_h - \lambda_v^\alpha i_v .$$

**Theorem.**
1. Solutions starting in $\mathbb{R}^5_+$ remain nonnegative.
2. The disease-free equilibrium is $F_0 = (1,0,0,1,0)$, and the next-generation matrix gives

$$R_0 = \sqrt{\frac{a^{2\alpha}\, b\, m\, c}{\lambda_v^\alpha\,(\nu^\alpha + r^\alpha + \lambda_h^\alpha + \delta^\alpha)}} .$$

3. $F_0$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
4. At an endemic equilibrium $F_\ast$, after eliminating $r_h$ and $s_v$ through the conservation laws, let $g(x) = x^3 + b_1x^2 + b_2x + b_3$ be the characteristic polynomial of the reduced Jacobian and $D(g) = 18b_1b_2b_3 + (b_1b_2)^2 - 4b_3b_1^3 - 4b_2^3 - 27b_3^2$ its discriminant. Then $F_\ast$ is locally asymptotically stable if $D(g) > 0$ and the Routh–Hurwitz conditions hold; or if $D(g) < 0$, $b_1, b_2 \ge 0$, $b_3 > 0$ and $\alpha < 2/3$; or if $D(g) < 0$, $b_1, b_2 > 0$ and $b_1b_2 = b_3$ for any $\alpha \in (0,1)$. It is unstable if $D(g) < 0$, $b_1 < 0$, $b_2 < 0$ and $\alpha > 2/3$.

## Expansion

Positivity follows from the generalised mean value theorem for Caputo derivatives: if $D^\alpha w \ge 0$ on an interval then $w$ is nondecreasing there, and each right-hand side is nonnegative on the corresponding coordinate face. Local stability of an equilibrium of a commensurate fractional system holds when every Jacobian eigenvalue satisfies $|\arg\lambda| > \alpha\pi/2$ (Matignon's criterion), which is weaker than $\mathrm{Re}\,\lambda < 0$ for $\alpha < 1$. At $F_0$ three eigenvalues are $-\lambda_h^\alpha$, $-(\lambda_h^\alpha + \gamma^\alpha)$ and $-\lambda_v^\alpha$; the infection block has trace $-(\nu^\alpha + r^\alpha + \lambda_h^\alpha + \delta^\alpha + \lambda_v^\alpha) < 0$ and determinant $\lambda_v^\alpha(\nu^\alpha + r^\alpha + \lambda_h^\alpha + \delta^\alpha)(1 - R_0^2)$, which is positive exactly when $R_0 < 1$. The square root in $R_0$ reflects the two-step human–mosquito–human transmission cycle. For the endemic state, the cubic criteria of Ahmed, El-Sayed and El-Saka show that a fractional order below $2/3$ can stabilise an equilibrium that would be unstable in the integer-order model.

## Sources

- E. Okyere, F. T. Oduro, S. K. Amponsah, I. K. Dontwi, N. K. Frempong, "Fractional Order Malaria Model With Temporary Immunity", arXiv:1603.06416 (2016), Sections "Model Derivation", "Non-negative Solutions" and "Analysis of Model Equilibria" (basic reproduction number, local stability of the disease-free and endemic equilibria), <https://doi.org/10.48550/arXiv.1603.06416>.
