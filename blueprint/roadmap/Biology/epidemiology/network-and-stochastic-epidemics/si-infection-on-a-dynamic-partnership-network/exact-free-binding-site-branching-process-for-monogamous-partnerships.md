# Exact free-binding-site branching process for monogamous partnerships

**Network.** Individuals enter a sexually active population at rate $\mu N$ and leave at rate $\mu$; each has $n$ binding sites. Free sites pair at rate $\rho/(nN)$ per pair, partnerships separate at rate $\sigma$, and entrants arrive with a $\mathrm{Bin}(n,p_{\mathrm{in}})$ number of partners. Stationarity of the number of partners requires the free-site fraction $F=1-p_{\mathrm{in}}$ to solve $\rho F^2=\sigma(1-F)$, i.e.

$$F=\frac{-\sigma+\sqrt{\sigma^2+4\rho\sigma}}{2\rho},$$

and as $N\to\infty$ the empirical free-site fraction follows $\dot F=-\rho F^2+\sigma(1-F)-2\mu(p_{\mathrm{in}}-(1-F))$, whose stable equilibrium is this $F$. An SI infection is transmitted at rate $\beta$ within each infected–susceptible partnership.

**Naive approximation.** Treating infected binding sites as independent offspring gives offspring mean

$$R_0=\frac{\beta(1-F)\bigl((\sigma+\mu)^2+(n-1)(\sigma+2\mu)(\sigma+\mu+\mu F)\bigr)}{\mu(\sigma+\mu+\mu F)(\beta+\sigma+2\mu)},$$

and, for $n=1$ and an ancestor without a partner, extinction probability $q_\phi=\frac{1}{R_0}-\frac{\mu(R_0-1)}{(\sigma+\mu)R_0}$. This process is not an asymptotically exact approximation, even for $n=1$: the fates of an infector and its infectee are dependent.

**Theorem (exact process for $n=1$).** Follow free binding sites of infected individuals instead. Each free site independently produces $Y\in\{0,1,2\}$ new free sites, with

$$\mathbb P(Y=0)=\frac{\mu(\sigma+\mu+(\beta+\mu)F)}{(\sigma(1-F)+\mu)(\beta+\sigma+2\mu)},\quad \mathbb P(Y=2)=\frac{\sigma\beta(\sigma+\mu)(1-F)}{(\sigma(1-F)+\mu)(\sigma+2\mu)(\beta+\sigma+2\mu)},$$

and $\mathbb P(Y=1)=1-\mathbb P(Y=0)-\mathbb P(Y=2)$. This Galton–Watson process is asymptotically exact as $N\to\infty$. Its threshold parameter is

$$\hat R_0=\mathbb E(Y)=\frac{(\sigma+\mu)^2(\sigma+2\mu+2\beta)(1-F)}{(\sigma(1-F)+\mu)(\sigma+2\mu)(\beta+\sigma+2\mu)},$$

and the probability of a minor outbreak from one infected individual with a free site is

$$\hat q_\phi=\min\Bigl(1,\frac{\mu(\sigma+2\mu)(\sigma+\mu+(\beta+\mu)F)}{\sigma\beta(\sigma+\mu)(1-F)}\Bigr)=\min\Bigl(1,\frac1{R_0}-\frac{\mu(R_0-1)}{\sigma R_0}\Bigr).$$

Hence, for $R_0>1$, $q_\phi=\hat q_\phi+\frac{\mu^2(R_0-1)}{\sigma(\sigma+\mu)R_0}>\hat q_\phi$: ignoring the dependence overestimates the probability of a minor outbreak.

## Expansion

From a free site an infected individual either dies (rate $\mu$, no offspring) or acquires a susceptible partner at rate $\rho F+\mu(1-F)/F=(\sigma+\mu)(1-F)/F$. An infected–susceptible pair ends by separation or the partner's death (one new free site), by the infected's death (none), or turns into an infected–infected pair by transmission; that pair ends by separation (two new free sites) or one death (one). Each newly freed site starts an independent, identically distributed history, because with $n=1$ nothing else links the two individuals afterwards; this gives the law of $Y$ and the extinction probability as the minimal root of $s=\mathbb P(Y=0)+\mathbb P(Y=1)s+\mathbb P(Y=2)s^2$. Eliminating $\beta$ through the $n=1$ case of the $R_0$ formula expresses $\hat q_\phi$ through $R_0$. For $n>1$ the death of an individual frees several partners simultaneously, and no such exact construction is known.

## Sources

- A. A. Lashari and P. Trapman, "Branching process approach for epidemics in dynamic partnership network", Journal of Mathematical Biology 76(1) (2018) 265–294, <https://doi.org/10.1007/s00285-017-1147-0>, PMCID PMC5754507. Lemma 1, Eqs. (1)–(5), (7)–(9) and the comparison of extinction probabilities in Section 3.
