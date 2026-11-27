# Under perfect confounding shifted parameters give the same data law

Assume perfect confounding: $\mathrm{batch}(d) = a + b\, \mathrm{cond}(d)$ for every donor $d$, for
real $a$ and $b$. Let $\mu$ be a probability measure on $\Omega$ and $U$ a noise process
$U_i : \Omega \to \mathbb{R}$, one for each cell $i = (d, c)$, and let the noise vector
$\omega \mapsto (U_i(\omega))_i$ be $\mu$-almost everywhere measurable. Then for all real $\mu_0$,
$\tau$, $\beta$ and $t$ the [data law](data-law.md) under $(\mu_0 + a t, \tau + b t, \beta - t)$
equals the data law under $(\mu_0, \tau, \beta)$.
