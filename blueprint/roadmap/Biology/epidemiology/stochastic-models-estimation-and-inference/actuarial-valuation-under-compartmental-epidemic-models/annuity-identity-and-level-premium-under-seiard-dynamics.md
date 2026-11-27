# Annuity identity and level premium for infectious-disease insurance under SEIARD dynamics

**Model.** Let $s,e,i,a,r,d$ be the fractions of a population that are susceptible, exposed, symptomatic infected, asymptomatic infected, recovered and dead, interpreted as the probabilities that a randomly chosen policyholder is in each state. Without vital dynamics,

$$\begin{aligned} s'&=-\beta\tfrac{N}{N_L}\,s\,(i+\kappa a), & e'&=\beta\tfrac{N}{N_L}\,s\,(i+\kappa a)-\alpha e,\\ i'&=p\alpha e-(\gamma_I+\delta_I)i, & a'&=(1-p)\alpha e-(\gamma_A+\delta_A)a,\\ r'&=\gamma_Ii+\gamma_Aa, & d'&=\delta_Ii+\delta_Aa, \end{aligned}$$

with incubation rate $\alpha$, symptomatic fraction $p$, relative infectiousness $\kappa$ of asymptomatic cases, recovery rates $\gamma_\cdot$ and disease death rates $\delta_\cdot$. For nonnegative data summing to one, the solution is global, nonnegative and bounded.

**Insurance plan.** Premiums are paid continuously at a level rate by policyholders in states $s$ and $e$; benefits are paid at unit rate to infected policyholders ($i$ or $a$) and stop at death. With force of interest $\delta>0$, the actuarial present values over an infinite horizon are

$$\bar a^{\,s+e}_{\overline\infty|}=\int_0^\infty e^{-\delta t}\big(s(t)+e(t)\big)\,dt,\qquad \bar a^{\,i+a}_{\overline\infty|}=\int_0^\infty e^{-\delta t}\big(i(t)+a(t)\big)\,dt,$$

and the equivalence principle gives the level premium $\bar P=\bar a^{\,i+a}_{\overline\infty|}/\bar a^{\,s+e}_{\overline\infty|}$.

**Proposition (annuity identity).** If $\gamma_I=\gamma_A$, $\delta_I=\delta_A$ and the initial state has $s_0+e_0+i_0+a_0=1$ (no one initially removed), then

$$\bar a^{\,s+e}_{\overline\infty|}+\Big(1+\frac{\gamma_I+\delta_I}{\delta}\Big)\bar a^{\,i+a}_{\overline\infty|}=\frac1\delta .$$

Consequently the level premium is determined by the benefit annuity alone:

$$\bar P=\frac{\delta\,\bar a^{\,i+a}_{\overline\infty|}}{1-(\delta+\gamma_I+\delta_I)\,\bar a^{\,i+a}_{\overline\infty|}} .$$

## Expansion

Adding the first four equations, the infection terms cancel and $(s+e+i+a)'=-(\gamma_I+\delta_I)(i+a)$ under equal removal rates. Integrating from $0$ gives $s+e+i+a-1=-(\gamma_I+\delta_I)\int_0^t(i+a)$. Multiplying by $e^{-\delta t}$, integrating over $(0,\infty)$ and using $\int_0^\infty e^{-\delta t}\int_0^tf\,d\tau\,dt=\frac1\delta\int_0^\infty e^{-\delta\tau}f(\tau)\,d\tau$ yields the identity. It is the epidemic analogue of the life-insurance relation $\bar a+\bar A/\delta\cdot\delta=1/\delta$: money not yet paid as premiums is accounted for by time spent infected, discounted at the removal-plus-interest rate. Unlike multiple-decrement life tables, the decrements here are coupled through the force of infection $\beta\frac{N}{N_L}(i+\kappa a)$, so premiums and reserves depend on the epidemic trajectory.

## Sources

- Achraf Zinihi, Matthias Ehrhardt, Moulay Rchid Sidi Ammi, "Actuarial Analysis of an Infectious Disease Insurance Based on an SEIARD Epidemiological Model", North American Actuarial Journal (2026), 1–22, <https://doi.org/10.1080/10920277.2026.2664588>. Published version of arXiv:2508.06580, cited next; locators there refer to the arXiv version.
- Achraf Zinihi, Matthias Ehrhardt, Moulay Rchid Sidi Ammi, "Actuarial Analysis of an Infectious Disease Insurance based on an SEIARD Epidemiological Model", arXiv:2508.06580 (2025): model (2.3)–(2.4) and its normalized form (3.1), Proposition 1 and Corollary 1 (well-posedness), Section 3.1 (premiums, benefits and the annuity relation). <https://doi.org/10.48550/arXiv.2508.06580>
