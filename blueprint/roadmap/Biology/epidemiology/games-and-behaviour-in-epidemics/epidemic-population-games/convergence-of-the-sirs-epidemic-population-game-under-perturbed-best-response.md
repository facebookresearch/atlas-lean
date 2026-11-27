# Convergence of the SIRS epidemic population game under perturbed best response dynamics

**Agents and learning rule.** Agents choose among $n$ strategies; strategy $\ell$ induces transmission rate $\vec\beta_\ell>0$, with $\vec\beta_1<\dots<\vec\beta_n$. The population state $x(t)$ lies in the simplex $\mathbb X=\{x\in[0,1]^n:\sum_ix_i=1\}$ and the mean transmission rate is $\mathcal B(t)=\vec\beta^{\top}x(t)$. Strategy costs $c_\ell(I)$ depend continuously on the infectious fraction $I$, with $c_1(I)>\dots>c_n(I)$, and $\tilde c_i(I)=c_i(I)-c_n(I)$. The payoff is $p=r-c(I)$ for a planner-chosen reward vector $r$. Under perturbed best response (PBR) the choice function is

$$C(p)=\operatorname{arg\,max}_{z\in\operatorname{int}\mathbb X}\big(z^{\top}p-Q(z)\big),$$

where the admissible perturbation $Q$ is $C^2$, strictly convex on the tangent space of $\mathbb X$, and has $\|\nabla Q(z)\|\to\infty$ as $\min_iz_i\to0$; the logit rule $C_i(p)=e^{p_i/\mu}/\sum_\ell e^{p_\ell/\mu}$ corresponds to $Q(x)=\mu\sum_ix_i\ln x_i$, $\mu>0$. The PBR evolutionary dynamics are $\dot x=C(p)-x$.

**Epidemic and payoff mechanism.** The normalized SIRS model is

$$\dot I=\big(\mathcal B(1-I-R)-\sigma\big)I,\qquad \dot R=\gamma I-\omega R,\qquad \sigma=\gamma+\theta,\quad \omega=\psi+\theta,$$

with recovery rate $\gamma$, waning rate $\psi$ and birth rate $\theta$; put $\eta=\omega/(\omega+\gamma)$. For a target $\bar\beta\in(\sigma,\vec\beta_n)$ and stationary reward $\bar r\in\mathbb R^n_{\ge0}$, let $\bar I=\eta(1-\sigma/\bar\beta)$, $\hat I=\eta(1-\sigma/\mathcal B)$, $\hat R=(1-\eta)(1-\sigma/\mathcal B)$. The planner's scalar state $q$ and reward are

$$\dot q=\kappa\Big((\hat I-I)+\eta(\ln I-\ln\hat I)+\upsilon^2(\bar\beta-\mathcal B)+\frac{\mathcal B}{\gamma}(R-\hat R)(1-\eta-R)\Big),\qquad r=q\vec\beta+\bar r+\tilde c(I)-\tilde c(\bar I),$$

with gains $\kappa,\upsilon>0$.

**Optimal endemic transmission rate.** Given a budget $c^*>0$, $\beta^*$ is the minimum of $\beta$ over $\beta\in(\sigma,\vec\beta_n)$, $r\in\mathbb R^n_{\ge0}$, $I\in[0,1]$ subject to $r^{\top}C(r-\tilde c(I))\le c^*$, $\beta=\vec\beta^{\top}C(r-\tilde c(I))$ and $I=\eta(1-\sigma/\beta)$; let $(\beta^*,r^*,I^*)$ attain it.

**Theorem (global convergence).** Suppose $\mathcal B(t)\ge\mathcal B_{\min}$ for all $t\ge0$, for some $\sigma<\mathcal B_{\min}<\bar\beta$. Then for the closed loop of the SIRS model, the PBR dynamics and the payoff mechanism, from any $I(0)\in(0,1]$, $R(0)\in[0,1-I(0)]$, $x(0)\in\mathbb X$, $q(0)\in\mathbb R$:

1. $q(t)\to\bar q$ and $\mathcal B(t)\to\bar\beta$, where $\bar q$ is the unique solution of $\bar\beta=\vec\beta^{\top}C(\bar q\vec\beta+\bar r-\tilde c(\bar I))$;
2. $I(t)\to\eta(1-\sigma/\bar\beta)$, $R(t)\to(1-\eta)(1-\sigma/\bar\beta)$ and $x(t)\to C(\bar q\vec\beta+\bar r-\tilde c(\bar I))$.

**Corollary (budget-optimal endemic state).** With $\bar r=r^*$ and $\bar\beta=\beta^*$ (and $\sigma<\mathcal B_{\min}<\beta^*$), $\mathcal B(t)\to\beta^*$, $I(t)\to I^*$ and $r(t)\to r^*$, and the long-run average reward satisfies $r^{*\top}C(r^*-\tilde c(I^*))\le c^*$.

**Local rate.** For the logit rule and $\upsilon$ small enough the closed loop is locally exponentially stable.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

The PBR dynamics are $\delta$-passive with storage function $\mathcal S(x,p)=\max_{z}(z^{\top}p-Q(z))-(x^{\top}p-Q(x))\ge0$, which vanishes exactly at rest points and satisfies $\nabla_x\mathcal S^{\top}\dot x+\nabla_p\mathcal S^{\top}\dot p\le\dot p^{\top}\dot x$. The payoff mechanism is designed so that the epidemic-plus-planner subsystem admits a matching storage function $\mathscr S$ in the scaled variables $(\mathcal BI,\mathcal BR,\mathcal B)$; the sum $\kappa^{-1}\mathcal S+\mathscr S$ is then nonincreasing along trajectories, and LaSalle's invariance principle gives convergence to the unique rest point. The lower bound $\mathcal B\ge\mathcal B_{\min}>\sigma$ keeps $\ln I-\ln\hat I$ controlled (it holds automatically with $\mathcal B_{\min}=\vec\beta_1$ when $\vec\beta_1>\sigma$). At the budget-optimal design $\bar q=0$, so the reward converges to $r^*$. The same Lyapunov function yields an anytime bound: $I(t)\le\bar I\,\pi_\upsilon(\alpha_\kappa)$ for all $t$, where $\pi_\upsilon(\alpha)=\bar I^{-1}\sup\{I:\mathscr S\le\alpha\}$ and $\alpha_\kappa=\kappa^{-1}\mathcal S(x(0),p(0))+\mathscr S(0)$, so a faster planner (larger $\kappa$) and a smaller weight $\upsilon$ reduce the overshoot of infections after an incentive revision. When the logit noise level $\mu$ is unknown, the source also estimates it from observed strategy choices.

## Sources

- Shinkyu Park, Jair Certorio, Nuno C. Martins, Richard J. La, "Epidemic Population Games and Perturbed Best Response Dynamics", IEEE Transactions on Automatic Control 70 (2025), 6036–6049, <https://doi.org/10.1109/tac.2025.3554601>. Published version of arXiv:2401.15475, cited next; locators there refer to the arXiv version.
- S. Park, J. Certorio, N. C. Martins and R. J. La, "Epidemic population games and perturbed best response dynamics", arXiv:2401.15475 (2024), Section 1.2 (PBR learning rule and the epidemic population game), Definition 1 (optimal endemic transmission rate), Section 3 (payoff mechanism, Theorem 1, Proposition 1, Corollary 1; Section 3.2 anytime bound) and the appendices (proofs), <https://doi.org/10.48550/arXiv.2401.15475>.
