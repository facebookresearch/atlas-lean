# Epidemic thresholds of SIS dynamics on time-varying networks

**Setting.** $n$ individuals follow SIS dynamics with homogeneous per-contact infection rate $\lambda$ and recovery rate $\mu$, but the contact network changes in time. Three standard regimes give explicit thresholds.

**Theorem (annealed regime).** If the network changes much faster than the epidemic and the average network $\bar{\mathcal{G}}$ is uncorrelated ($\bar a_{ij} \propto \bar k_i \bar k_j$), with degree moments $\langle \bar k \rangle = \frac1n\sum_i \bar k_i$ and $\langle \bar k^2\rangle = \frac1n \sum_i \bar k_i^2$, then as $n \to \infty$ the disease-free equilibrium is asymptotically stable if

$$\frac{\lambda}{\mu} < \sigma_{\mathrm{ann}} = \frac{\langle \bar k\rangle}{\langle \bar k^2\rangle}$$

and unstable if $\lambda/\mu > \sigma_{\mathrm{ann}}$. In particular, for scale-free degree distributions with exponent in $(2,3]$, $\langle \bar k^2\rangle \to \infty$ and the threshold vanishes.

**Theorem (periodic switching).** For the discrete-time SIS model on a periodically repeated sequence of adjacency matrices $A_1,\dots,A_T$, the disease-free equilibrium is asymptotically stable (fast eradication) when the spectral radius of

$$P = \prod_{t=1}^{T}\big((1-\mu)I + \lambda A_t\big)$$

is below $1$, and the disease becomes endemic when $\rho(P) > 1$.

**Theorem (activity-driven networks).** At each step every individual $i$ independently activates with probability $a_i$ and, if active, creates $m$ undirected links to individuals chosen uniformly at random; all links are removed at the next step. With $\langle a\rangle$ and $\langle a^2\rangle$ the first two moments of the activity distribution, let

$$\sigma_{\mathrm{ADN}} = \frac{1}{m\big(\langle a\rangle + \sqrt{\langle a^2\rangle}\big)}.$$

If $\lambda/\mu < \sigma_{\mathrm{ADN}}$ the epidemic is quickly eradicated with probability tending to $1$ as $n \to \infty$, and if $\lambda/\mu > \sigma_{\mathrm{ADN}}$ it becomes endemic with probability tending to $1$.

## Expansion

All three thresholds come from linearising the SIS dynamics at the disease-free state and asking whether the resulting positive linear (or switched linear) system grows. In the annealed case the linearisation is driven by the average adjacency matrix, whose rank-one structure $\bar k \bar k^\top/(n\langle\bar k\rangle)$ has spectral radius $\langle \bar k^2\rangle/\langle \bar k\rangle$; this replaces the static quenched threshold $\lambda/\mu = 1/\rho(A)$. For periodic switching the one-period monodromy matrix $P$ plays the role of $\rho(A)$. In an activity-driven network, the linearised dynamics of infected individuals grouped by activity close on two moments, $\langle i \rangle$ and $\langle a\,i\rangle$, because infection travels both from active infected nodes (rate $\propto a_i$) and onto susceptibles who become active; the leading eigenvalue of the resulting $2\times2$ system is $m\lambda(\langle a\rangle + \sqrt{\langle a^2\rangle})$, which gives $\sigma_{\mathrm{ADN}}$. Heterogeneous activity therefore lowers the threshold, but less dramatically than heterogeneous static degree, because contacts are not concentrated on persistent hubs.

## Sources

- Lorenzo Zino, Ming Cao, "Analysis, Prediction, and Control of Epidemics: A Survey from Scalar to Dynamic Network Models", IEEE Circuits and Systems Magazine 21 (2021), 4–23, <https://doi.org/10.1109/mcas.2021.3118100>. Published version of arXiv:2103.00181, cited next; locators there refer to the arXiv version.
- Lorenzo Zino, Ming Cao, "Analysis, Prediction, and Control of Epidemics: A Survey from Scalar to Dynamic Network Models", arXiv:2103.00181 (2021), Section 3 ("Epidemics models on dynamic networks": time-scale separation and Theorem 4, temporal-switching networks, activity-driven networks and Theorem 5), <https://doi.org/10.48550/arXiv.2103.00181>.
