# Probability density of the extended sampled tree on stratigraphic ranges

Consider the fossilized birth–death process with speciation rate $\lambda > 0$, extinction rate $\mu \ge 0$, fossil-sampling rate $\psi > 0$, extant sampling probability $\rho \in (0,1]$ and origin time $x_0$, under *asymmetric (budding) speciation*: at each speciation the ancestral species continues and one new species buds off. Group the samples of each sampled species into a *stratigraphic range* from its oldest sample at time $o_i$ to its youngest at $y_i$ (times before the present). Let $d_i \ge 0$ be the extinction time of species $i$ ($d_i = 0$ if it survives) and $b_i$ the time at which its lineage branched off its sampled ancestor ($b_i = x_0$ for the founding range). The *extended stratigraphic range* is the interval $[d_i, o_i]$, and the *oriented extended sampled tree* $\mathcal T$ is the reconstructed tree on these extended ranges with ancestor/descendant orientation kept. Let $n$ be the number of ranges, $k$ the number of fossil samples, $m$ the number of ranges with $d_i > 0$, and $l$ the number of ranges with an extant sample.

**Complete sampling.** If $\mu = 0$ and $\rho = 1$,

$$f[\mathcal T \mid \lambda, \mu, \psi, \rho, x_0] = \psi^k \lambda^{n-1} \prod_{i=1}^n e^{-(\lambda+\psi) b_i}.$$

**General case.** For arbitrary parameters,

$$f[\mathcal T \mid \lambda, \mu, \psi, \rho, x_0] = \frac{\psi^k \mu^m \rho^l (1-\rho)^{n-m-l}}{\lambda\,(1 - p(x_0))} \prod_{i=1}^n \lambda\, \frac{\tilde q(o_i)}{\tilde q(d_i)}\, \frac{q(b_i)}{q(o_i)}, \tag{1}$$

where

$$c_1 = \sqrt{(\lambda-\mu-\psi)^2 + 4\lambda\psi}, \qquad c_2 = -\frac{\lambda - \mu - 2\lambda\rho - \psi}{c_1},$$

$$p(t) = 1 + \frac{-(\lambda-\mu-\psi) + c_1 \dfrac{e^{-c_1 t}(1-c_2) - (1+c_2)}{e^{-c_1 t}(1-c_2) + (1+c_2)}}{2\lambda}, \qquad q(t) = \frac{4 e^{-c_1 t}}{\bigl(e^{-c_1 t}(1-c_2) + (1+c_2)\bigr)^2},$$

$$\tilde q(t) = \sqrt{e^{-(\lambda+\mu+\psi)t}\, q(t)} .$$

The density depends on the fossils only through their number $k$ and the times $b_i, o_i, d_i$, not on the individual fossil ages inside a range.

## Expansion

$p(t)$, the probability that a lineage alive at time $t$ leaves no sampled descendant, solves $p' = \mu - (\lambda+\mu+\psi)p + \lambda p^2$ with $p(0) = 1-\rho$. Along an extended range, between $d_i$ and $o_i$, only unobserved buds that leave no samples are allowed, so the density obeys $Q' = -(\lambda+\mu+\psi)Q + \lambda p Q$, solved by $\tilde q$ with $\tilde q(0) = 1$. Its initial value at $d_i$ is $\mu$ for an extinct species, $\rho$ for a sampled extant one and $1-\rho$ for an unsampled extant one. Between $o_i$ and $b_i$ the lineage may change species unobserved, which doubles the speciation term, $Q' = -(\lambda+\mu+\psi)Q + 2\lambda p Q$, solved by $q$. Multiplying these factors over ranges, a factor $\lambda$ per bud and $\psi$ per fossil, and conditioning on at least one sample by dividing by $1 - p(x_0)$, gives (1). Under complete sampling $p \equiv 0$, $\tilde q(t) = e^{-(\lambda+\psi)t}$, and (1) reduces to the first formula, in which each range contributes only its waiting time with no event since its birth. The ranges, not individual fossils, are the units of the likelihood, which makes the model usable for range data without a phylogeny.

## Sources

- T. Stadler, A. Gavryushkina, R. C. M. Warnock, A. J. Drummond, T. A. Heath, "The fossilized birth–death model for the analysis of stratigraphic range data under different speciation modes", *Journal of Theoretical Biology* (2018), Sections 3.1–3.3, Theorem 1 and Theorem 2 (Eqs. (1)–(5)) with proof, <https://doi.org/10.1016/j.jtbi.2018.03.005> (PMC5931795).
