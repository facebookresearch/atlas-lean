# Observability of the epidemic state from molecular and serology testing

**Setting.** A system $\dot x=g(x,\beta(t))$ with time-varying parameter $\beta(t)$ and output $y=h(x)$ is *observable* if identical outputs $y_1\equiv y_2$ force equal initial states $x_1(0)=x_2(0)$ and equal parameters $\beta_1\equiv\beta_2$.

Consider the SIR model with molecular testing at rate $\theta(t)$ (sensitivity $\eta$), state $(s,i_u,i_d,r)$, where only detected infections are recorded. In the augmented model, everyone is additionally tested at a constant baseline rate $\theta_B$ with sensitivity $\eta_{BI}$ for current and $\eta_{BR}$ for past infection (serology), and recovered individuals are split into undetected $r_u$ and detected $r_d$:

$$
\begin{aligned}
\dot s&=-\beta(t)si_u,&\dot i_u&=\beta(t)si_u-\gamma i_u-\eta\theta(t)i_u-\theta_B\eta_{BI}i_u,\\
\dot i_d&=\eta\theta(t)i_u+\theta_B\eta_{BI}i_u-\gamma i_d,&\dot r_u&=\gamma i_u-\theta_B\eta_{BR}r_u,\qquad r_d=1-s-i_u-i_d-r_u .
\end{aligned}
$$

**Theorem.** Assume $\gamma$ is known.

1. *(Molecular testing only.)* With output $y=i_d$ and $\eta\theta(t)>0$: if $\beta$ is constant the system is observable; if $\beta(t)$ is time-varying it is not observable.
2. *(Adding serology.)* With output $y=(i_d,r_d)$ and $\eta\theta(t)+\eta_{BR}\theta_B>0$, the system is observable even for time-varying $\beta(t)$.

## Expansion

From $i_d$ and its derivative one recovers $i_u=(\dot i_d+\gamma i_d)/(\eta\theta)$ (adjusting for baseline detection), but the susceptible fraction enters only through the product $\beta(t)s(t)$ in $\dot i_u$. A time-varying $\beta$ can absorb any change in $s$, so $s$ (and hence the distance to herd immunity, which the optimal policy needs) is not determined by molecular data alone. Serology measures past infection: $\dot r_d=\gamma i_d+\theta_B\eta_{BR}r_u$ determines $r_u$ from $r_d$ and $i_d$, and conservation then gives $s=1-i_u-i_d-r_u-r_d$, after which $\beta(t)=-\dot s/(si_u)$ is identified. Molecular tests are highly sensitive but have a short detectability window; low-sensitivity baseline serology is what makes the adaptive policy implementable, and stochastic simulations show large savings over non-adaptive testing.

## Depends on

- [Three-phase optimal testing policy for the SIR model with detection](three-phase-optimal-testing-policy-for-the-sir-model-with-detection.md)

## Sources

- D. Acemoglu, A. Fallah, A. Giometto, D. Huttenlocher, A. Ozdaglar, F. Parise, S. Pattathil, "Optimal adaptive testing for epidemic control: combining molecular and serology tests", arXiv:2101.00773 (2021), Section 4 (Materials and Methods): definition of observability, Lemma 1 (molecular testing) and Lemma 2 (serology testing), <https://doi.org/10.48550/arXiv.2101.00773>.
