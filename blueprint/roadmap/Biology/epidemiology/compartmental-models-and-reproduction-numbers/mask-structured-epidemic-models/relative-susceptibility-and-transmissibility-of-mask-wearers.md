# Relative susceptibility and transmissibility of mask wearers

**Model.** A closed, randomly mixing population of size $N$ follows SEIRD dynamics with compartments susceptible ($S$), exposed ($E$), presymptomatic ($I_P$), asymptomatic or mild ($I_A$), symptomatic ($I_S$), recovered ($R$) and dead ($D$). Each compartment is split into mask wearers and non-wearers. A susceptible wearer has relative susceptibility $r_s \in [0,1]$ and an infectious wearer relative transmissibility $r_t \in [0,1]$ compared with non-wearers; $1 - r_s$ is the mask's *protection* and $1 - r_t$ its *containment*. The force of infection on a susceptible is therefore multiplied by $r_s$ if it wears a mask and each infectious contribution by $r_t$ if the infective wears one.

**Proposition (universal adoption).** If the whole population wears masks, the basic reproduction number is reduced by the factor $r_t r_s$:

$$R_0^{\mathrm{mask}} = r_t\, r_s\, R_0 .$$

A face covering with $5\%$ protection and $5\%$ containment reduces $R_0 = 2.5$ to $2.5 \times 0.95^2 \approx 2.26$.

**Corollary (partial coverage).** If a fraction $f$ of the population wears masks, independently of infection status, and mixing is proportional, the next-generation matrix between non-wearers and wearers is rank one and

$$R_0(f) = R_0\,\big[(1-f) + f\,r_s r_t\big].$$

**Demand model.** In the supply-and-demand variant, the per-capita demand of healthy and asymptomatic individuals depends on reported symptomatic cases through the logistic function

$$\omega_A = \frac{1}{1 + e^{-k_1(I_S - k_2)}},$$

with $k_1$ the rate of demand increase and $k_2$ the number of reported cases at which half the population seeks masks.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

With wearer status fixed, an infective of status $j \in \{0, 1\}$ (non-wearer, wearer) produces new infections in status $i$ at rate proportional to $R_0\, s_i\, t_j\, N_i/N$, where $s_0 = t_0 = 1$, $s_1 = r_s$, $t_1 = r_t$, $N_1/N = f$. The next-generation matrix $K_{ij} = R_0 s_i (N_i/N)\, t_j$ is the outer product of $a_i = R_0 s_i N_i/N$ and $b_j = t_j$, so $\rho(K) = \sum_i a_i b_i = R_0[(1-f) + f r_s r_t]$; at $f = 1$ this is the universal-adoption factor. Only the product $r_s r_t$ enters, so protection and containment are interchangeable for $R_0$ under random allocation, while targeted allocation (masks for the elderly and for detected symptomatic cases) exploits the difference between them; in the source's simulations, random distribution is consistently the least effective use of a limited supply.

## Sources

- C. J. Worby and H.-H. Chang, "Face mask use in the general population and optimal resource allocation during the COVID-19 pandemic", Nature Communications 11 (2020) 4049, Methods ("Compartmental models", "Supply & demand model") and Results ("Universal face covering in public can further reduce cases"), <https://doi.org/10.1038/s41467-020-17922-x> (PMC7426871).
