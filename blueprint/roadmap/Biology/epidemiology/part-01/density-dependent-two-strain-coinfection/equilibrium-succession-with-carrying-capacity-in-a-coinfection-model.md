# Equilibrium succession with carrying capacity in a density-dependent coinfection model

**Model.** Let $S$ be susceptibles, $I_1, I_2$ hosts infected by strain $1$ or $2$ only, and $I_{12}$ coinfected hosts. With intrinsic growth rate $r > 0$, carrying capacity $K > 0$, transmission rates $\alpha_1, \alpha_2, \alpha_3$ (strain 1, strain 2, both strains), removal rates $\mu_i = \rho_i + d_i$ (recovery plus death), rates $\gamma_1, \gamma_2$ at which singly infected hosts acquire the other strain, $\bar\gamma = \gamma_1 + \gamma_2$, and rates $\eta_1, \eta_2$ at which singly infected hosts are coinfected by contact with $I_{12}$,

$$\begin{aligned}
S' &= \big(r(1 - S/K) - \alpha_1 I_1 - \alpha_2 I_2 - \alpha_3 I_{12}\big) S,\\
I_1' &= (\alpha_1 S - \eta_1 I_{12} - \gamma_1 I_2 - \mu_1) I_1,\\
I_2' &= (\alpha_2 S - \eta_2 I_{12} - \gamma_2 I_1 - \mu_2) I_2,\\
I_{12}' &= (\alpha_3 S + \eta_1 I_1 + \eta_2 I_2 - \mu_3) I_{12} + \bar\gamma I_1 I_2 .
\end{aligned}$$

Put $\sigma_i = \mu_i/\alpha_i$ and assume $\sigma_1 < \sigma_2 < \sigma_3$ (strain 1 spreads most easily in a naive population; coinfection has the smallest reproduction number), and $\Delta_\alpha = \eta_1\alpha_2 - \eta_2\alpha_1 \ne 0$. Define

$$A_1 = \frac{\alpha_1\alpha_3(\sigma_3 - \sigma_1)}{r}, \quad A_2 = \frac{\alpha_2\alpha_3(\sigma_3 - \sigma_2)}{r}, \qquad \eta_1^* = \frac{\eta_1}{A_1}, \quad \eta_2^* = \frac{\eta_2}{A_2}.$$

Equilibria are written $G_{ijk}$, with $i,j,k \in \{0,1\}$ indicating whether $I_1, I_2, I_{12}$ are non-zero; $G_{000} = (K,0,0,0)$ is disease-free.

**Single strain (Proposition 1).** With only $I_i$ present, $R_0(I_i) = K/\sigma_i$; the disease-free state is stable for $K < \sigma_i$ and the endemic state $\big(\sigma_i, \tfrac{r}{\alpha_i}(1 - \sigma_i/K)\big)$ for $K > \sigma_i$.

**Theorem 1.** Assume $0 < \eta_1^* < \max\{1, \eta_2^*\}$. For every $K$ off the thresholds below there is exactly one locally stable non-negative equilibrium, and as $K$ increases it follows one of two routes:

1. if $\eta_1^* < 1$: $G_{000} \to G_{100}$, with $G_{000}$ stable for $K < \sigma_1$ and $G_{100}$ stable for $K > \sigma_1$;
2. if $1 < \eta_1^* < \eta_2^*$: $G_{000} \to G_{100} \to G_{101} \to G_{001}$, with $G_{000}$ stable for $K < \sigma_1$, $G_{100}$ for $\sigma_1 < K < K_1$, the coinfection state $G_{101}$ for $K_1 < K < K_2$ and the coinfection-only state $G_{001}$ for $K > K_2$, where

$$K_1 = \frac{\sigma_1\eta_1^*}{\eta_1^* - 1}, \qquad K_2 = \frac{\sigma_3}{\sigma_1}K_1 .$$

At each threshold the outgoing and incoming equilibria coincide (exchange of stability), and strain 2 alone never becomes the stable state in this regime.

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

Every equilibrium with $I_1 \ne 0$ and $I_2 = 0$ has $\alpha_1 S = \mu_1 + \eta_1 I_{12}$, so $S^* \ge \sigma_1$, and the susceptible equation pins $r(1 - S^*/K) = \alpha_1 I_1 + \alpha_3 I_{12}$. Along $G_{100}$ the coinfected class can invade once $\alpha_3\sigma_1 + \eta_1 I_1^* > \mu_3$; substituting $I_1^* = \frac{r}{\alpha_1}(1 - \sigma_1/K)$ gives $K > K_1$, which is finite and positive only when $\eta_1^* > 1$, that is when contact with coinfected hosts is fast enough relative to the scale $A_1$. On $G_{101}$ the $I_1$-coordinate vanishes at $K = K_2$, where the branch joins $G_{001} = (\sigma_3, 0, 0, \tfrac{r}{\alpha_3}(1 - \sigma_3/K))$. Stability of $G_{101}$ reduces, by the block structure of its Jacobian, to the invasion condition for strain 2, $\alpha_2 S^* - \eta_2 I_{12}^* - \gamma_2 I_1^* - \mu_2 < 0$, the remaining $3 \times 3$ block being stable by the Routh–Hurwitz criterion; the hypothesis $\eta_1^* < \eta_2^*$ secures this condition throughout $K_1 < K < K_2$.

## Sources

- J. Andersson, S. Ghersheen, V. Kozlov, V. G. Tkachev, U. Wennergren, "Effect of density dependence on coinfection dynamics", Analysis and Mathematical Physics (2021), Eqs. (1)–(13), (22), Proposition 1, Theorem 1 and Corollaries 3 and 6, <https://doi.org/10.1007/s13324-021-00570-9>, PMCID PMC8452503.
