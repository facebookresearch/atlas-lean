# Feedback lockdown policies versus optimal control in the SIR model with congestion mortality

**Model.** Fractions $s,i,r$ follow the SIR model with a lockdown $L(t)\in[0,1]$ entering quadratically (pairwise contacts):

$$\dot s=-\beta(1-L)^2si,\qquad \dot i=\beta(1-L)^2si-\gamma i,\qquad \dot r=\gamma i .$$

The planner pays the economic cost $L$ plus a death cost $\kappa\gamma_d(i)i$ with congestion-dependent lethality $\gamma_d(i)=\gamma_0+\gamma_1i$, so the running cost is $L+\kappa\gamma_1i^2+\kappa\gamma_0i$ and the objective is $\int_0^Tc\,dt$. The uncontrolled reproduction number is $R(t)=\beta s(t)/\gamma$; herd immunity is the first time $t^*$ with $s(t^*)\le\gamma/\beta$.

**Two feedback policies.**
- *Policy A (target reproduction number $\rho$):* while $\beta s/\gamma>\rho$ impose $L_\rho$ with $\frac\beta\gamma(1-L_\rho)^2s=\rho$, so $\dot i=(\rho-1)\gamma i$; afterwards no lockdown.
- *Policy B (target prevalence $\iota$):* no lockdown until $i=\iota$; then hold $i\equiv\iota$ by choosing $L_\iota$ with $\beta(1-L_\iota)^2s\iota=\gamma\iota$ until herd immunity; then release.

**Lemma (uncontrolled phases in closed form).** On any interval $[a,b]$ with $L\equiv0$,

$$\int_a^bi^2\,dt=\gamma\frac{[\ln s(a)]^2-[\ln s(b)]^2}{2\beta^2}-\frac{s(a)-s(b)}{\beta}+\Bigl(s(a)+i(a)-\frac\gamma\beta\ln s(a)\Bigr)\frac{r(b)-r(a)}{\gamma},$$

and $\int_a^bi\,dt=(r(b)-r(a))/\gamma$. Hence for $T=\infty$ the total costs $C_A(\rho)$ and $C_B(\iota)$ are explicit functions of the targets, with final sizes given by the SIR final-size relation.

**Theorem.** Let $T=\infty$. For every control with no lockdown after herd immunity, the cost is at least

$$C^*=\min_{0\le i^*\le i_{\max}}U(i^*),\qquad i_{\max}=i_0+s_0-\frac\gamma\beta\Bigl(1-\ln\frac{\gamma}{\beta s_0}\Bigr),$$

where $U(i^*)$ is an explicit sum of a lower bound on pre-herd-immunity cost (using $\epsilon=\sqrt{27/32}$), the uncontrolled post-herd-immunity cost from the lemma and the linear death term $\frac{\kappa\gamma_0}{\gamma}(r(\infty)-r_0)$. Consequently the optimality gaps of the two policies at their best targets are certified:

$$C_A(\rho^*)-C_{\rm opt}\le\min_\rho C_A(\rho)-C^*,\qquad C_B(\iota^*)-C_{\rm opt}\le\min_\iota C_B(\iota)-C^* .$$

The optimal lockdown is increasing in the force of infection $\beta si$, not in $R(t)$, so it vanishes when $i\to0$ even if $R\gg1$. Numerically the optimal policy undergoes a phase transition from suppression (short horizon or high $\kappa$) to mitigation (long horizon), and in the mitigation regime Policy B is close to the lower bound and beats Policy A: holding $R<1$ indefinitely, as spectral control prescribes, is suboptimal over long horizons.

## Expansion

Without control, $\frac{di}{ds}=-1+\frac{\gamma}{\beta s}$ and $dt=-\frac{ds}{\beta si}$, so $i\,dt=-\frac{ds}{\beta s}$ and $i^2dt=-\frac{i\,ds}{\beta s}$ with $i=s(a)+i(a)-s+\frac\gamma\beta\ln\frac{s}{s(a)}$; integrating in $s$ gives the lemma. Under Policy A the controlled phase has exponential $i$ and $\dot s=-\rho\gamma i$; under Policy B the controlled phase has constant $i=\iota$ and lockdown $1-\sqrt{\gamma/(\beta s)}$, whose integral is explicit. For the lower bound, before herd immunity the economic and quadratic death costs are combined pointwise by an AM–GM-type inequality in $L$ and $i$, which yields the $\epsilon\sqrt{\kappa\gamma_1}$ term.

## Sources

- Leonardo Cianfanelli, Francesca Parise, Daron Acemoglu, Giacomo Como, Asuman Ozdaglar, "Lockdown interventions in SIR models: Is the reproduction number the right control variable?", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 4254–4259, <https://doi.org/10.1109/cdc45484.2021.9682977>. Published version of arXiv:2112.06546, cited next; locators there refer to the arXiv version.
- L. Cianfanelli, F. Parise, D. Acemoglu, G. Como, "Lockdown interventions in SIR model: Is the reproduction number the right control variable?", arXiv:2112.06546 (2021), Section 2 (model and optimal control problem), Section 3 (Policies A and B), Section 4 (Lemma 1, Propositions 1–3, Theorems 1–2) and the numerical phase-transition results. <https://doi.org/10.48550/arXiv.2112.06546>
