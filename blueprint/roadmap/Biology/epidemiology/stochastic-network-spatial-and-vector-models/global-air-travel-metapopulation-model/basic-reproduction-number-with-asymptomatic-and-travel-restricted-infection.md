# Basic reproduction number with asymptomatic and travel-restricted infection

Consider the within-city influenza scheme with compartments $S$ (susceptible), $L$ (latent), $I_t$ (symptomatic, allowed to travel), $I_{nt}$ (symptomatic, not travelling), $I_a$ (asymptomatic) and $R$ (recovered), in a population of size $N$ without vital dynamics:

- susceptibles are infected at rate $\beta\,(I_t + I_{nt} + r_\beta I_a)\,S/N$, with relative infectiousness $r_\beta \in [0, 1]$ of asymptomatic cases, and enter $L$;
- latent individuals become infectious at rate $\varepsilon$; a fraction $p_a$ become asymptomatic and the rest symptomatic, of whom a fraction $p_t$ travel and $1 - p_t$ do not;
- all infectious classes recover at rate $\mu$.

Then the basic reproduction number, the spectral radius of the next-generation matrix at the disease-free equilibrium $S = N$, is

$$\mathcal R_0 \;=\; \frac{\beta}{\mu}\,\bigl(1 - p_a + r_\beta\, p_a\bigr),$$

independent of $\varepsilon$ and $p_t$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Order the infected compartments as $(L, I_t, I_{nt}, I_a)$. New infections enter only $L$, so the new-infection matrix $F$ has a single nonzero row, $(0, \beta, \beta, r_\beta\beta)$. The transition matrix $V$ is lower triangular with diagonal $(\varepsilon, \mu, \mu, \mu)$ and off-diagonal entries $-(1-p_a)p_t\varepsilon$, $-(1-p_a)(1-p_t)\varepsilon$, $-p_a\varepsilon$ in the $L$ column. Since $F$ has rank one, the spectral radius of $FV^{-1}$ is its only nonzero eigenvalue, the $(L, L)$ entry: the expected number of new infections produced by one latent individual over its life, namely $\beta/\mu$ times the probability of becoming symptomatic plus $r_\beta\beta/\mu$ times the probability of becoming asymptomatic. The latency rate only delays transmission, and the travel split only relocates it. With $p_a = 0.33$ and $r_\beta = 0.5$, $\mathcal R_0 \approx 0.835\,\beta/\mu$. The worldwide simulations show that therapeutic antiviral use might mitigate such a pandemic up to $\mathcal R_0 \approx 1.9$ if drugs are available in all countries, and that cooperative sharing of stockpiles outperforms national use.

## Sources

- V. Colizza, A. Barrat, M. Barthélemy, A.-J. Valleron, A. Vespignani, "Modeling the worldwide spread of pandemic influenza: baseline case and containment interventions", *PLoS Medicine* 4(1) (2007) e13, Methods, "The Model" and "Reproductive Number R0", <https://doi.org/10.1371/journal.pmed.0040013> (PMC1779816).
