# Diffusion approximation and scaling invariance of the mRNA–protein reporter model

**Mean model (Eq. 1).** Let $M(t)$ and $P(t)$ be the abundances of a reporter mRNA and its protein, with a non-negative transcription function $\tau(t)$, translation rate $\alpha>0$ and degradation rates $\delta_m,\delta_p>0$:

$$\frac{dM}{dt}=\tau(t)-\delta_m M,\qquad \frac{dP}{dt}=\alpha M-\delta_p P.$$

**Scaling invariance.** If only $\tilde M=s_M M$ and $\tilde P=s_P P$ are observed for unknown factors $s_M,s_P>0$, then $(\tilde M,\tilde P)$ solves the same system with $\tilde\tau=s_M\tau$ and $\tilde\alpha=(s_P/s_M)\alpha$ and unchanged $\delta_m,\delta_p$. Hence from proportional measurements the degradation rates are invariant under the rescaling, while $\tau$ and $\alpha$ are determined only up to the measurement scales.

**Diffusion approximation (Eq. 2).** Treating transcription, translation and degradation as birth and death events of individual molecules, measured in units proportional to molecule numbers, gives the Itô system

$$dM=\zeta_M\,dt+\sigma_M\,dW_M,\qquad dP=\zeta_P\,dt+\sigma_P\,dW_P,$$

with drifts $\zeta_M=\tau(t)-\delta_m M$, $\zeta_P=\alpha M-\delta_p P$, volatilities $\sigma_M=s_M^{1/2}(\tau(t)+\delta_m M)^{1/2}$, $\sigma_P=s_P^{1/2}(\alpha M+\delta_p P)^{1/2}$, and independent Wiener processes $W_M,W_P$. The noise scale therefore carries information about the conversion factors $s_M,s_P$ that the mean model cannot identify.

**Euler likelihood (Eq. 4).** For observations $y_i=(M(t_i),P(t_i))$ with small $\Delta t_i=t_{i+1}-t_i$, the transition density is approximated by a bivariate normal with mean $y_i+(\zeta_M,\zeta_P)\Delta t_i$ and covariance $\mathrm{diag}(\sigma_M^2,\sigma_P^2)\Delta t_i$, all evaluated at $y_i$, and the likelihood is the product of these densities over $i$.

## Expansion

Each reaction channel contributes its rate to the drift with the sign of its stoichiometric change and the same rate to the variance per unit time, which yields $\tau+\delta_m M$ and $\alpha M+\delta_p P$; mRNA and protein events change different species, so the noise terms are independent. When molecules are measured in units $1/s$ of a molecule, each event changes the measured quantity by $s$, multiplying the variance by $s$ relative to the scaled rates, which is the factor $s_M^{1/2}$, $s_P^{1/2}$. In the companion mean-ODE approach the same solution path is used as the mean of a chosen observation distribution, with initial conditions as extra parameters; both likelihoods feed a Bayesian posterior sampled by MCMC, with latent bridge points inserted between sparse observations.

## Sources

- B. Finkenstädt, E. A. Heron, M. Komorowski, K. Edwards, S. Tang, C. V. Harper, J. R. E. Davis, M. R. H. White, A. J. Millar, D. A. Rand, "Reconstruction of transcriptional dynamics from gene reporter data using differential equations", Bioinformatics (2008). <https://doi.org/10.1093/bioinformatics/btn562>, PMCID PMC2639297. Section 2, Eqs. (1)–(5).
