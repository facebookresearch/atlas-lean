# Three-phase optimal testing policy for the SIR model with detection

**Model.** Population fractions are susceptible $s$, infected-undetected $i_u$ (circulating), infected-detected $i_d$ (isolated) and recovered $r=1-s-i_u-i_d$. Molecular tests are applied at rate $\theta(t)\ge0$ with sensitivity $\eta$; detected individuals are isolated:

$$
\dot s=-\beta(t)si_u,\qquad \dot i_u=\beta(t)si_u-\gamma i_u-\eta\theta(t)i_u,\qquad \dot i_d=\eta\theta(t)i_u-\gamma i_d .
$$

**Control problem.** Minimize total testing subject to a prevalence cap:

$$
\min_{\theta(\cdot)\ge0}\int_0^\infty\theta(t)\,dt\qquad\text{subject to}\qquad i_u(t)\le i_{\max}\ \ \text{for all }t .
$$

**Theorem.** Let $\beta$ be constant (or, more generally, a non-increasing function of time). The optimal policy $\theta^\dagger$ has three phases:

1. while $i_u(t)<i_{\max}$, do not test: $\theta^\dagger(t)=0$;
2. once $i_u$ reaches $i_{\max}$, hold it there with the feedback rate

$$
\theta^\dagger(t)=\frac{\beta(t)s(t)-\gamma}{\eta};
$$

3. once herd immunity is reached, i.e. $s(t)=\gamma/\beta(t)$ for the first time, stop testing.

Under $\theta^\dagger$ herd immunity is reached at a finite time $t_{\rm herd}$, after which $\theta^\dagger\equiv0$; if the optimal cost is positive then $i_u(t_{\rm herd})=i_{\max}$. The optimal control is a most-rapid-approach path to herd immunity.

## Expansion

Testing is only useful for lowering $i_u$, and every unit of time spent below the cap is a unit of time in which susceptibles are not being depleted towards the herd-immunity level $\gamma/\beta$. Since the epidemic must eventually reach $s\le\gamma/\beta$ for testing to stop, the cheapest path lets the epidemic grow freely up to the cap and then rides the constraint boundary $i_u=i_{\max}$, where $\dot i_u=0$ requires exactly $\eta\theta=\beta s-\gamma$; along this boundary $s$ decreases at the maximal admissible rate $\beta si_{\max}$. Once $\beta s\le\gamma$ the epidemic declines on its own. The total cost is therefore $\frac{1}{\eta}\int_{\text{phase 2}}(\beta s-\gamma)\,dt$, and a monotone $\beta(t)$ preserves the argument. The policy is adaptive: it needs the current epidemic state $s(t)$, which motivates the separate question of state estimation.

## Sources

- D. Acemoglu, A. Fallah, A. Giometto, D. Huttenlocher, A. Ozdaglar, F. Parise, S. Pattathil, "Optimal adaptive testing for epidemic control: combining molecular and serology tests", arXiv:2101.00773 (2021), Section 2 (model, optimization problem and Theorem 1), Supplementary Materials (Theorem 2 for non-increasing $\beta(t)$ and Lemmas 3–5), <https://doi.org/10.48550/arXiv.2101.00773>.
