# Optimal transmission reduction with ICU saturation and a herd-immunity target

**Setting.** Consider $s'=-b(t)si$, $i'=b(t)si-\gamma i$ on $\mathbb{T}=\{s+i\le1\}$, where the effective contact rate $b(t)\in[\beta_*,\beta]$ is lowered from its natural value $\beta$ by non-pharmaceutical interventions. Given a horizon $t_f$ and $(s_0,i_0)$ in the viable set $\mathcal{B}$ of [Viable and no-effort sets of the SIR model under an ICU constraint](viable-and-no-effort-sets-of-the-sir-model-under-an-icu-constraint.md), minimize

$$J(t_f,b)=\int_0^{t_f}\big[\lambda_1+\lambda_2(\beta-b(t))\big]\,dt,\qquad \lambda_2>0,$$

subject to the ICU constraint $(s(t),i(t))\in\mathcal{B}$ and the herd-immunity target $s(t_f)<\gamma/\beta$, so that the epidemic can be released without further effort. Let $\mathcal{A}$ be the no-effort set, $\mathcal{B}_0=([0,\gamma/\beta_*]\times[0,i_M])\cap\mathbb{T}$, and $\Phi_\mathcal{B}$ the boundary of $\mathcal{B}$.

**Theorem.** Let $s_0,i_0>0$, $(s_0,i_0)\in\mathcal{B}$.

1. If $(s_0,i_0)\in\mathcal{A}$ and $t_f$ is large enough, the unique optimal control is no intervention, $b\equiv\beta$, with value $\lambda_1t_f$.
2. In general an optimal control is

$$b^{opt}(t)=\begin{cases}\beta,& t\in(0,\tau_1\wedge\tau_0),\\ \beta_*,& t\in(\tau_0,\tau_1)\ \text{if }\tau_0<\tau_1,\\ \dfrac{\beta}{1+\beta i_M(\tau_2-t)},& t\in(\tau_1,\tau_2),\\ \beta,& t>\tau_2,\end{cases}$$

where $\tau_0$ is the first time the uncontrolled trajectory hits the viability boundary $\partial\mathcal{B}$, $\tau_1$ is the time the resulting trajectory reaches the ICU capacity $i=i_M$, and $\tau_2=\tau_1+\big(s(\tau_1)-\gamma/\beta\big)/(\gamma i_M)$ is the time at which $s$ reaches $\gamma/\beta$. On $(\tau_1,\tau_2)$ the infected fraction is held exactly at $i_M$: $b(t)=\gamma/s(t)$ and $s$ decreases linearly at rate $\gamma i_M$.

3. In feedback form: no intervention in the interior of $\mathcal{B}$ and on $\partial\mathcal{A}$; maximal intervention $\beta_*$ on $\partial\mathcal{B}\setminus\mathcal{B}_0$; and $b=\gamma/s$ on the saturation segment $(\gamma/\beta,\gamma/\beta_*)\times\{i_M\}$. This control is optimal for every $t_f$ beyond the time it needs to reach $s=\gamma/\beta$, and it is unique up to a Lebesgue-null set.

## Expansion

The strategy is "do nothing until forced, then ride the ICU limit". Intervening early is wasted because the epidemic has not yet consumed susceptibles; the cheapest way to reach herd immunity without breaching capacity is to let infections rise to $i_M$ and then hold $i'=0$, which requires $b\,s=\gamma$ and makes $s'=-\gamma i_M$ constant. Only if the uncontrolled trajectory would leave the viable set before reaching $i_M$ must full lockdown $\beta_*$ be applied along the viability boundary. The proof works with the relaxed target $s(t_f)\le\gamma/\beta-\varepsilon$, establishes existence and lower semicontinuity of the value function, and characterizes Pontryagin extremals with a state constraint: singular arcs force $i=i_M$, and the multiplier of the state constraint is a measure supported where the constraint binds.

## Depends on

- [Viable and no-effort sets of the SIR model under an ICU constraint](viable-and-no-effort-sets-of-the-sir-model-under-an-icu-constraint.md)

## Sources

- Florin Avram, Lorenzo Freddi, Dan Goreac, "Optimal Control of a SIR Epidemic With ICU Constraints and Target Objectives", arXiv:2108.10589 (2021): Section 3 (strict and relaxed no-effort problem formulations and existence proposition), Section 4 (Pontryagin conditions; singular-arc theorem; constant-$i$ proposition), Section 5 (extremals in the no-effort zone and outside it; main optimal control theorem with feedback form). <https://doi.org/10.48550/arXiv.2108.10589> Published version: Applied Mathematics and Computation 418 (2022) 126816, <https://doi.org/10.1016/j.amc.2021.126816>.
