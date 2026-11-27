# Under perfect confounding the condition effect is not identifiable

Assume perfect confounding: $\mathrm{batch}(d) = a + b\, \mathrm{cond}(d)$ for every donor $d$, for
real $a$ and $b \ne 0$. Let $\mu$ be a probability measure on $\Omega$ and $U$ a noise process
$U_i : \Omega \to \mathbb{R}$, one for each cell $i = (d, c)$, and let the noise vector
$\omega \mapsto (U_i(\omega))_i$ be $\mu$-almost everywhere measurable. Then no map $F$ from
measures on $\mathbb{R}^{\delta \times \kappa}$ to $\mathbb{R}$ recovers the condition effect from
the [data law](data-law.md): there is no $F$ with
$F(\text{data law at } (\mu_0, \tau, \beta)) = \tau$ for all real $\mu_0$, $\tau$, $\beta$.
Pseudobulk values, being functions of the data, do not help.
