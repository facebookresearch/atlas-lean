# Perfect confounding trades batch effect for condition effect

Assume perfect confounding: $\mathrm{batch}(d) = a + b\, \mathrm{cond}(d)$ for every donor $d$, for
real $a$ and $b$. Then for all real $\mu_0$, $\tau$, $\beta$, $t$ and every noise process
$U_i : \Omega \to \mathbb{R}$, one for each cell $i = (d, c)$, the [observed cell values](obs.md)
under the parameters $(\mu_0 + a t, \tau + b t, \beta - t)$ equal those under
$(\mu_0, \tau, \beta)$, at every cell and every $\omega$: the donor means agree.
