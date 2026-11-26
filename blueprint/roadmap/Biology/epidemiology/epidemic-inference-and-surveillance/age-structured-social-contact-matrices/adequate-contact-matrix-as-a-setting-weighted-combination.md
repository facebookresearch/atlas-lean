# Adequate contact matrix as a setting-weighted combination

Consider a synthetic population with $N_a$ individuals in age class $a$, partitioned into settings $k \in \{H, S, W, C\}$ (households, schools, workplaces, general community). Within each household, school or workplace mixing is assumed homogeneous: every member contacts every other member of the same unit. Aggregating units gives setting-specific matrices $M^k_{ab} \ge 0$, the relative frequency of contacts of an individual of age $a$ with individuals of age $b$ in setting $k$; in the general community mixing is homogeneous, so the columns of $M^C$ are proportional to the class sizes $N_b$.

Let $r_k \ge 0$, $\sum_k r_k = 1$, be the fraction of effective (transmission-relevant) contacts that occur in setting $k$, and let $\Theta$ be the total rate of effective contacts. Choosing weights $\omega_k$ so that

$$\omega_k \sum_{a,b} N_a M^k_{ab} = r_k\, \Theta \quad\text{for every } k, \qquad\text{i.e.}\qquad \omega_k = \frac{r_k\, \Theta}{\sum_{a,b} N_a M^k_{ab}},$$

the adequate contact matrix is the linear combination

$$M = \sum_k \omega_k M^k .$$

In the age-structured SIR model with age-independent transmissibility $\beta$ and recovery rate $\gamma$, susceptibles of class $a$ experience the force of infection $\lambda_a(t) = \beta \sum_b M_{ab}\, I_b(t) / N_b$.

Properties:

- $M$ is determined up to the scalar $\Theta$, which is absorbed into $\beta$; the setting proportions $r_k$ fix the relative contributions of the settings;
- $M^C$ has rank one: $M^C_{ab} = c_a N_b$ for some $c_a \ge 0$;
- linearizing at the disease-free state gives the next-generation matrix $K_{ab} = (\beta/\gamma)\, N_a M_{ab} / N_b$, i.e. $K = (\beta/\gamma)\, D M D^{-1}$ with $D = \mathrm{diag}(N_a)$; similar matrices share their spectrum, so

$$R_0 = \rho(K) = \frac{\beta}{\gamma}\, \rho(M),$$

the spectral radius of the contact matrix scaled by $\beta / \gamma$;
- under fully homogeneous mixing, $M_{ab} = c\, N_b / N$ with $N = \sum_b N_b$, which has rank one and $\rho(M) = c$, recovering the classical $R_0 = \beta c / \gamma$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The homogeneous-within-unit assumption replaces unavailable contact diaries by census information on household composition, school attendance and employment, and the resulting matrices reproduce the strong age assortativity and the parent–child secondary diagonals seen in diary surveys. Baseline proportions for influenza-like illness are $r_H = 0.30$, $r_S = 0.18$, $r_W = 0.19$ and $r_C = 0.33$. The similarity argument for $R_0$ shows that rescaling class sizes does not change the threshold once $M$ is fixed; what changes $R_0$ across countries is the structure of $M$ itself, which inherits each country's demography.

## Sources

- L. Fumanelli, M. Ajelli, P. Manfredi, A. Vespignani, S. Merler, "Inferring the structure of social contacts from demographic data in the analysis of infectious diseases spread", PLoS Computational Biology 8(9) (2012) e1002673, Materials and Methods, "Computing contact matrices" and "SIR model with heterogeneous mixing patterns", Eq. (1), <https://doi.org/10.1371/journal.pcbi.1002673> (PMC3441445).
