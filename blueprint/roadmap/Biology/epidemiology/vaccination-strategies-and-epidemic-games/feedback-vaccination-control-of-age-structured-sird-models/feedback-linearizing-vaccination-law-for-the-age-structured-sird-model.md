# Feedback-linearizing vaccination law for the age-structured SIRD model

**Model.** With $n$ age classes, the susceptible, infected, recovered and deceased counts satisfy, for $k = 1,\dots,n$,

$$\dot S_k = -\lambda S_k\sum_{j=1}^n \frac{M_{kj}I_j}{N_j} - p_k\theta_k S_k, \qquad \dot I_k = \lambda S_k\sum_{j=1}^n \frac{M_{kj}I_j}{N_j} - (\gamma_{R_k} + \gamma_{D_k})I_k,$$

$$\dot R_k = \gamma_{R_k}I_k + p_k\theta_k S_k, \qquad \dot D_k = \gamma_{D_k}I_k,$$

where $M_{kj}$ is the contact rate between classes, $\lambda$ the transmission probability, $\gamma_{R_k}, \gamma_{D_k}$ recovery and death rates, $N_k$ the (constant) class size, and $\theta_k(t) \ge 0$ a vaccination rate with efficacy $p_k$.

**Open-loop facts.** For nonnegative inputs the box $B$ of admissible states is positively invariant. For any nonnegative locally Lipschitz feedback $\theta_k = \Theta_k(x)$, the set of disease-free equilibria $\{x \in B : I_k = 0,\ \theta_k S_k = 0\}$ is pointwise attractive: every trajectory converges to one such equilibrium. For one age class, if $I(0) \ge 1$ and $S(0) > \gamma/\alpha := N(\gamma_R + \gamma_D)/(\lambda M)$ (so the epidemic initially grows), any input that is positive on some initial interval $[0,\delta]$ and nonnegative afterwards strictly lowers the epidemic peak $\max_t I(t)$ compared with no vaccination.

**Theorem (exponential decay under the linearizing feedback).** On $\mathcal{D} = \{S_k \ne 0,\ \sum_j M_{kj}I_j/N_j \ne 0\}$ the system with outputs $h_k = I_k$ has full relative degree, and the coordinates $z_{1k} = I_k$, $z_{2k} = \dot I_k$ (without control) transform it into a normal form. The state feedback

$$\theta_k = \frac{v_k - L_f^2 h_k}{L_{g_k}L_f h_k}, \qquad v_k = -\alpha^k_2 z_{2k} - \alpha^k_1 z_{1k},$$

with $\alpha^k_1, \alpha^k_2 > 0$, yields the linear closed loop $\ddot I_k + \alpha^k_2\dot I_k + \alpha^k_1 I_k = 0$. As long as the state remains in $\mathcal{D}$, $I_k(t) \le C_k I_k(0)e^{-\mu_k t}$ for some $C_k, \mu_k > 0$, and $S_k, R_k, D_k$ converge. If moreover, with $\Gamma = \max_k(\gamma_{R_k} + \gamma_{D_k})$,

$$\alpha^k_1 > (\gamma_{R_k} + \gamma_{D_k})\Big(\Gamma + \sum_j M_{kj}\Big), \qquad \alpha^k_2 = \gamma_{R_k} + \gamma_{D_k} + \Gamma + \sum_j M_{kj},$$

then the input is nonnegative and $B$ remains forward invariant.

**Saturated and observer-based versions.** Because the linearizing gain blows up as $\sum_j M_{kj}I_j \to 0$, the law is replaced by a Lipschitz saturated feedback, equal to a smoothed version of the linearizing law where $S_k \ge \tilde S_k$ and $I_k \ge \tilde I_k$ and to $0$ elsewhere, bounded by $\theta_{\sup}$; with the gains above it keeps the disease-free set pointwise attractive and $S_k, R_k, D_k$ convergent. Using only measured infected counts, a high-gain observer with gains $(\beta^i_1/\epsilon, \beta^i_2/\epsilon^2, \beta^i_3/\epsilon^3)$, where $s^3 + \beta^i_1 s^2 + \beta^i_2 s + \beta^i_3$ is Hurwitz, recovers the same attractivity of the disease-free equilibrium set for all sufficiently small $\epsilon > 0$.

## Expansion

The control enters $\dot S_k$, so $I_k$ has relative degree two: $\ddot I_k = L_f^2 h_k + L_{g_k}L_f h_k\,\theta_k$ with $L_{g_k}L_f h_k = -p_k\lambda S_k\sum_j M_{kj}I_j/N_j$, which is invertible exactly on $\mathcal{D}$. Assigning a Hurwitz second-order dynamics to each $I_k$ gives the exponential bound. Nonnegativity of $\theta_k$ follows from choosing $\alpha^k_2$ large enough that the required correction always removes susceptibles rather than adding them. The invariance lemma (a box with $\tilde S_k \le (\gamma_{R_k} + \gamma_{D_k})\tilde I_k/(\lambda\sum_j M_{kj})$ is forward invariant for any nonnegative input) justifies switching the control off once susceptibles are depleted. The high-gain observer argument uses the Lipschitz property of the saturated law and the triangular structure of the normal form.

## Sources

- Candy Sonveaux, Christophe Prieur, Gildas Besançon and Joseph J. Winkin, "Observer-based output feedback for an age-structured SIRD model", arXiv:2410.19481 (2024), Section 2 (model), Section 3 (positive invariance and attractivity propositions), Section 4 (peak-reduction proposition, the two theorems on exponential stability and nonnegativity, saturated-feedback proposition, invariance lemma) and Section 5 (high-gain observer theorem), <https://doi.org/10.48550/arXiv.2410.19481>. Published version: IEEE Transactions on Automatic Control 71 (2026) 583–589, <https://doi.org/10.1109/tac.2025.3600590>.
