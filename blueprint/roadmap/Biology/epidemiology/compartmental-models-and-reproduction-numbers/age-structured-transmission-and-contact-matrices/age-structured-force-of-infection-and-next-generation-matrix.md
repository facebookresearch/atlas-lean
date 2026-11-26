# Age-structured force of infection and next-generation matrix

**Model.** Divide a population into age groups $i = 1, \dots, n$ of sizes $N_i > 0$. Let $c_{ij} \ge 0$ be the mean rate at which an individual of group $i$ makes epidemiologically relevant contacts with individuals of group $j$, $\sigma_i \ge 0$ the relative susceptibility of group $i$, and $q > 0$ a transmissibility parameter (probability of transmission per contact for a fully susceptible contact). With $I_j(t)$ infectious individuals in group $j$, the force of infection on a susceptible of group $i$ is

$$\lambda_i(t) = q\,\sigma_i \sum_{j=1}^{n} c_{ij}\,\frac{I_j(t)}{N_j},$$

and new infections in group $i$ occur at rate $\lambda_i(t)\,S_i(t)$. Reciprocity of contacts requires $N_i c_{ij} = N_j c_{ji}$ (the total number of $i$–$j$ contacts counted from either side).

**Next-generation matrix.** For an SEIR-type natural history in which an infected individual of group $j$ is infectious for an expected duration $D_j$ (latent stages do not transmit), linearizing at the disease-free state $S_i = N_i$ gives the next-generation matrix

$$K_{ij} = q\,\sigma_i\, c_{ij}\, \frac{N_i}{N_j}\, D_j \qquad (i, j = 1, \dots, n),$$

the expected number of group-$i$ infections caused by one infectious individual of group $j$, and the basic reproduction number is its spectral radius

$$R_0 = \rho(K).$$

Consequences:

- $R_0$ is linear in $q$, so $q$ can be calibrated from a target $R_0$ once the contact structure is fixed: $q = R_0 / \rho(K|_{q=1})$.
- With $\sigma_i \equiv \sigma$ and $D_j \equiv D$, $K$ is similar to $q\sigma D\, C$ (via the diagonal matrix $\mathrm{diag}(N_i)$), so $R_0 = q\,\sigma\, D\, \rho(C)$ with $C = (c_{ij})$.
- If $K$ is irreducible (every age group can eventually infect every other), the Perron eigenvector of $K$ gives the age distribution of infections in the early exponential phase.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

Write the infected subsystem near the disease-free state as $\dot x = (\mathcal F - \mathcal V)x$, where $\mathcal F$ collects new infections and $\mathcal V$ the transitions between infected stages; $K = \mathcal F \mathcal V^{-1}$ restricted to the newly infected states. New infections in group $i$ come from infectious individuals of group $j$ at per-capita rate $q \sigma_i c_{ij} N_i / N_j$, and an individual stays infectious for expected time $D_j$, giving $K_{ij}$. The similarity claim follows from $K = q\sigma D\,\mathrm{diag}(N)\, C\, \mathrm{diag}(N)^{-1}$ in that case, and the spectral radius is invariant under similarity. In practice the contact matrix comes from diary surveys (for example POLYMOD); the influenza study resampled survey participants to produce alternative matrices and inferred $q$ and the $\sigma_i$ jointly with them by MCMC on surveillance data, and the COVID-19 lockdown study computed $R_0$ by the same next-generation approach on a model with prodromic, asymptomatic and symptomatic infectious stages of different infectiousness.

## Sources

- M. Baguelin, S. Flasche, A. Camacho, N. Demiris, E. Miller, W. J. Edmunds, "Assessing optimal target populations for influenza vaccination programmes: an evidence synthesis and modelling study", PLoS Medicine (2013), Methods (transmission model, age-group-specific force of infection, Eq. 4, with transmissibility $q$, contact rates $c_{ij}$ and susceptibilities $\sigma_i$; contact-matrix resampling), <https://doi.org/10.1371/journal.pmed.1001527> (PMC3793005).
- L. Di Domenico, G. Pullano, C. E. Sabbatini, P.-Y. Boëlle, V. Colizza, "Impact of lockdown on COVID-19 epidemic in Île-de-France and possible exit strategies", BMC Medicine (2020), Methods ("Mixing", "Compartmental model and transmission") and Results ($R_0$ by the next-generation approach), <https://doi.org/10.1186/s12916-020-01698-4> (PMC7391016).
