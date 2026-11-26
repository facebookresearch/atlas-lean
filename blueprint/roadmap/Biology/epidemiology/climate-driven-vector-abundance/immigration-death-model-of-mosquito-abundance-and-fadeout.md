# Immigration–death model of mosquito abundance and its fadeout probability

Let the number $M(t)$ of adult mosquitoes in an area be a continuous-time Markov chain on $\{0, 1, 2, \dots\}$ with transitions $M \to M + 1$ at rate $\lambda > 0$ (recruitment of new adults, which depends on rainfall $R$ and temperature $T$, $\lambda = \lambda(R, T)$) and $M \to M - 1$ at rate $\mu M$ (per-capita adult mortality $\mu = \mu(T) > 0$). Then, for every initial value $M(0) = m_0$,

$$\mathbb{E}\, z^{M(t)} = \bigl(1 + (z - 1) e^{-\mu t}\bigr)^{m_0} \exp\Bigl(\frac{\lambda}{\mu}(z - 1)\bigl(1 - e^{-\mu t}\bigr)\Bigr), \qquad |z| \le 1,$$

so $M(t)$ converges in distribution to the Poisson law with mean $\lambda / \mu$, independently of $m_0$. In particular the long-run probability of having no adult mosquitoes, used as the probability of local seasonal fadeout of the vector, is

$$\lim_{t \to \infty} \Pr\{M(t) = 0\} = e^{-\lambda(R, T)/\mu(T)} .$$

Replacing a fixed vector population size in a Ross–Macdonald-type basic reproduction number by its climatic equilibrium mean $\lambda / \mu$ makes $R_0$ depend on rainfall only through $\lambda$, since $R_0$ is proportional to the vector abundance.

## Expansion

Each of the $m_0$ initial adults is still alive at time $t$ independently with probability $e^{-\mu t}$, which gives the binomial factor. Recruits arrive as a Poisson process of rate $\lambda$, and a recruit born at time $s \le t$ is alive at $t$ with probability $e^{-\mu(t-s)}$; thinning a Poisson process gives a Poisson number of survivors with mean $\int_0^t \lambda e^{-\mu (t-s)} ds = (\lambda/\mu)(1 - e^{-\mu t})$, which gives the exponential factor. As $t \to \infty$ the first factor tends to $1$ and the second to the Poisson generating function $e^{(\lambda/\mu)(z-1)}$. Rainfall changes the breeding-site supply and so $\lambda$, while temperature enters both $\lambda$ and $\mu$; the vector fadeout probability is only an approximate proxy for pathogen fadeout because the transmission model on top of it is deterministic. In the same framework the temperature dependence of $R_0$ is dominated by the probability that a mosquito survives the extrinsic incubation period, giving a transmission optimum around 32–33 °C for both *P. falciparum* and *P. vivax*.

## Sources

- Parham PE, Michael E. Modeling the effects of weather and climate change on malaria transmission. *Environmental Health Perspectives* 118:620–626 (2010), Results, "Anopheles mosquito population dynamics" and "Malaria invasion dynamics". DOI <https://doi.org/10.1289/ehp.0901256>. PMCID PMC2866676.
