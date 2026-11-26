# Threshold quantities of the SEIRS epidemic in a birth–death population

**Setting.** Without disease the population is a supercritical linear birth–death process: each individual gives birth at rate $\lambda$ and dies at rate $\mu$, with $\lambda>\mu$. A Markovian, uniformly mixing SEIRS disease spreads in it with states $(S,E,I,R)$ and $N=S+E+I+R$: infection at rate $\kappa SI/N$, end of latency at rate $\nu$ per latent individual, recovery at rate $\delta$, extra disease death at rate $\sigma$ (infectives die at rate $\mu+\sigma$), and loss of immunity at rate $\rho$. Newborns are susceptible. Start with $n$ susceptibles and one latent individual, and let $L_n=E_n+I_n$.

**Theorem.**

1. As $n\to\infty$, $L_n$ converges weakly on finite time intervals to a two-type branching process $L_\infty$ in which latent individuals become infectious at rate $\nu$ or die at rate $\mu$, and infectious individuals create latent ones at rate $\kappa$ and leave at rate $\mu+\delta+\sigma$.

2. Its basic reproduction number and Malthusian parameter are

$$R_0=\frac{\nu\kappa}{(\mu+\nu)(\delta+\mu+\sigma)},\qquad \alpha=-\Big(\mu+\frac{\nu+\delta+\sigma}{2}\Big)+\sqrt{\frac{(\nu-\delta-\sigma)^2}{4}+\kappa\nu}.$$

These do not depend on $\rho$, so they are the same for the SEIR, SEIS and SEIRS models.

3. The probability of a minor outbreak starting from one latent individual is $\pi=1$ if $R_0\le1$ and

$$\pi=\frac{\mu}{\mu+\nu}+\frac{\nu}{\mu+\nu}\,\frac{1}{R_0}\qquad\text{if }R_0>1;$$

starting from $m$ latent and $k$ infectious individuals it is $\pi_{(m,k)}=\pi^m R_0^{-k}$ when $R_0>1$.

Here $\nu/(\mu+\nu)$ is the probability of surviving the latent period and $\kappa/(\mu+\delta+\sigma)$ the mean number of infectious contacts, so $R_0$ grows with $\kappa,\nu$ and falls with $\mu,\delta,\sigma$.

## Expansion

While infected individuals are few, almost every contact is with a susceptible, so infections form a branching process; the coupling with $L_\infty$ holds on finite intervals as $n\to\infty$. The mean offspring matrix of the two-type process has generator $\begin{pmatrix}-(\mu+\nu)&\nu\\ \kappa&-(\mu+\delta+\sigma)\end{pmatrix}$, whose largest eigenvalue is $\alpha$; $\alpha>0$ if and only if $R_0>1$. An infective's offspring count is geometric with mean $R_0$, so the extinction probability of a line started by an infective is $1/R_0$, and a latent individual either dies before becoming infectious, with probability $\mu/(\mu+\nu)$, or becomes an infective; this gives $\pi$, and independence of lines gives $\pi_{(m,k)}$, which agrees with Allen and Lahodny's SEIR result.

## Sources

- Tom Britton, Désiré Ouédraogo, "SEIRS epidemics in growing populations", arXiv:1703.09581 (2017): Section 2 (population and Markovian SEIRS model, event rates), Section 3 (branching approximation theorem, Malthusian parameter and $R_0$ theorems with remarks, minor-outbreak probability theorem and corollary). <https://doi.org/10.48550/arXiv.1703.09581> Published version: Mathematical Biosciences (2018), as *SEIRS epidemics with disease fatalities in growing populations*, <https://doi.org/10.1016/j.mbs.2017.11.006>.
