# Evolutionarily stable vaccination limits under dynamic vaccine availability

**Population model.** In a population with birth rate $b$, death rate $d<b$, recovery rate $r$ and infection rate $\lambda$ (normalized by population size), let $\theta$ and $\psi$ be the infected and vaccinated fractions, $\phi=1-\theta-\psi$ the susceptible fraction, and $\rho=\lambda/(r+b)$. Vaccines become available at the epochs of a Poisson process with *dynamic availability rate* $\nu_b+\nu_e\psi$ ($\nu_b>0$ basic rate, $\nu_e\ge0$ extra rate rewarding public uptake). At each availability epoch a susceptible individual vaccinates with probability $q$ given by the public vaccine-response. The jump process is approximated by an ODE whose locally stable equilibria with $q^*\in\{0,1\}$ are the candidate limits:

$$\theta^*_{\mathrm{nv}}=1-\frac1\rho,\qquad \psi^*_e=\frac{-(b+\nu_b-\nu_e)+\sqrt{(b+\nu_b-\nu_e)^2+4\nu_e\nu_b}}{2\nu_e}\ \ (\nu_e>0),\quad \psi^*_e=\frac{\nu_b}{b+\nu_b}\ \ (\nu_e=0),$$

$$\psi^*_o=\frac{\nu_b}{b\rho-\nu_e},\qquad \theta^*_o=\theta^*_{\mathrm{nv}}-\psi^*_o .$$

**Utilities.** If $k$ of $M$ influencers are vaccinated, an individual vaccinating with probability $q$ at equilibrium $(\theta,\psi)$ pays $u(q)=q\,h(\theta,\psi)+i_p(\theta,\psi)c_i+c_f(k)$, where $i_p(\theta,\psi)=\lambda\theta/(\lambda\theta+\nu_b+\nu_e\psi)$ is the probability of being infected before the next vaccine opportunity, $c_i$ is the cost of infection, $c_f(k)$ the cost of missing the vaccine, and

$$h(\theta,\psi)=c_{v_1}+\Bigl(1-\frac kM\Bigr)\min\Bigl\{\bar c_{v_2},\frac{c_{v_2}}{\psi}\Bigr\}-i_p(\theta,\psi)\,c_i-c_f(k)$$

is the net cost of vaccinating (side-effect costs fall as more influencers vaccinate). A vaccine-response is an ESSS if, at its equilibrium, its vaccination probability $q^*$ is the unique best response and remains so against invasion by any small fraction of static mutants. Set $h_i=h(\theta^*_{\mathrm{nv}},0)$, $h_v=h(0,\psi^*_e)$, $h^o_v=h(\theta^*_o,\psi^*_o)$.

**Classification.**

1. If $\rho\le1$, there is a self-eradicating ESSS with $q^*=0$ and limit $(0,0)$. Assume now $\rho>1$.
2. If $h_i>0$, there is a non-vaccinating ESSS with $q^*=0$ and endemic limit $(\theta^*_{\mathrm{nv}},0)$.
3. If $h_v<0$ and $\nu_e>b\rho-\nu_b/\theta^*_{\mathrm{nv}}$, there is an eradicating ESSS with $q^*=1$ and limit $(0,\psi^*_e)$.
4. If $h^o_v<0$ and $0\le\nu_e<b\rho-\nu_b/\theta^*_{\mathrm{nv}}$, there is a co-occurring ESSS with $q^*=1$ and limit $(\theta^*_o,\psi^*_o)$ (partial control).
5. Otherwise no ESSS exists.

The eradicating and co-occurring ESSS never coexist, but a non-vaccinating ESSS can coexist with either. Complete eradication (no endemic ESSS and an eradicating one) given $k$ vaccinated influencers holds exactly when $h_i\le0$, $h_v<0$ and $\nu_e>b\rho-\nu_b/\theta^*_{\mathrm{nv}}$. Both $h_i$ and $h_v$ decrease in $k$, so there is a smallest number of vaccinated influencers that guarantees eradication, which the leader targets through incentives.

## Expansion

1. With $q^*\in\{0,1\}$, the ODE equilibria solve linear or quadratic equations: $\theta$ is either $0$ or fixed by $1-\theta-\psi=1/\rho$, and $\psi$ balances vaccination inflow $(1-\theta-\psi)(\nu_b+\nu_e\psi)$ against outflow $b\psi$.
2. The utility is affine in $q$ with slope $h$, so $q^*=0$ is the strict best response iff $h>0$ and $q^*=1$ iff $h<0$; stability against small static-mutant fractions follows by continuity of $h$ and local asymptotic stability of the attractor.
3. The threshold $\nu_e$ versus $b\rho-\nu_b/\theta^*_{\mathrm{nv}}$ decides whether the infection-free equilibrium with full uptake is stable or whether the disease persists at $\theta^*_o>0$.

## Sources

- V. Singh, V. Kavitha, *Stochastic vaccination game among influencers, leader and public*, arXiv:2304.02380 (section "Population Game": the approximating ODE, the candidate attractor table, the utility function and the lemma classifying evolutionarily stable limits; eradication condition of Theorem 1). <https://doi.org/10.48550/arXiv.2304.02380> Published version: Dynamic Games and Applications 14 (2023) 1268–1316, <https://doi.org/10.1007/s13235-023-00531-w>.
