# Coalescent for exposed–infectious epidemics with latent periods

**Population model (EI model).** An epidemic with a latent stage is modeled forward in time $u$ as a continuous-time Markov jump process $\mathbf H(u)=(E(u),I(u))$ counting exposed (infected, not yet infectious) and infectious individuals, with transitions

$$
\begin{aligned}
(e,i)&\to(e+1,i) &&\text{at rate } \alpha(u)\,i \quad\text{(birth: new infection)},\\
(e,i)&\to(e-1,i+1) &&\text{at rate } \gamma\,e \quad\text{(migration: end of latent period)},\\
(e,i)&\to(e,i-1) &&\text{at rate } \nu\,i \quad\text{(death: removal)}.
\end{aligned}
$$

Here $1/\gamma$ is the mean latent period, $1/\nu$ the mean infectious period, and $\alpha$ is a continuous, time-varying per-capita transmission rate that absorbs depletion of susceptibles; the effective reproduction number is $R_u=\alpha(u)/\nu$. In the transmission tree, a birth splits an infectious lineage into one infectious and one exposed lineage, so in a sample genealogy **coalescence can only join an exposed lineage with an infectious one**: the model is a two-deme structured coalescent with between-deme coalescence only.

**Theorem (EI coalescent).** Let $\tilde E(t),\tilde I(t)$ be deterministic approximations of the population trajectories (for example, the ODE solution $\dot E=\alpha I-\gamma E$, $\dot I=\gamma E-\nu I$), written in backward time $t$ from the sampling time. Conditional on them, the numbers $\tilde{\mathbf C}(t)=(n_E,n_I)$ of exposed and infectious ancestral lineages of a sample form a continuous-time Markov chain with infinitesimal rates

$$
\begin{aligned}
(n_E,n_I)&\to(n_E-1,\,n_I) &&\text{at rate } n_E\,n_I\,\frac{\alpha(t)}{\tilde E(t)} \quad\text{(coalescence)},\\
(n_E,n_I)&\to(n_E+1,\,n_I-1) &&\text{at rate } n_I\,\frac{\gamma\,(\tilde E(t)+1)}{\tilde I(t)} \quad\text{(lineage becomes exposed)},\\
(n_E,n_I)&\to(n_E-1,\,n_I+1) &&\text{at rate } \mathbb 1\big(\tilde I(t)>n_I\big)\,n_E\,(\tilde I(t)-n_I)\,\frac{\alpha(t)}{\tilde E(t)} \quad\text{(coalescent migration)}.
\end{aligned}
$$

The third move is a birth that joins a sampled exposed lineage to an unsampled infectious one, which turns the sampled lineage infectious. The likelihood of an observed genealogy is the likelihood of this chain (with deterministic jumps at heterochronous sampling times) divided by the number of compatible labeled, colored tree topologies. Since only coalescence times are observed, the lineage states are latent and are imputed by data augmentation in Bayesian inference of $\alpha(t)$, hence of $\tilde I(t)$ and $R_t$.

## Depends on

- [Structured coalescent](../../coalescent-theory/structured-coalescent/README.md)

## Expansion

Given a full trajectory of $\mathbf H$ and sampled lineages at time $T$, each population event is resolved backward in time by uniform choice of the lineages involved. At a birth at time $u_i$, the probability that both participants are sampled is $\frac{n_E}{E(u_i)}\frac{n_I}{I(u_i)}$, that the exposed one is sampled and the infectious one is not is $\frac{n_E}{E(u_i)}\frac{I(u_i)-n_I}{I(u_i)}$, and otherwise the sample is unaffected; at a migration, a sampled infectious lineage is the one that was exposed with probability $n_I/I(u_i)$. Multiplying these marks into the population event rates, re-expressed through post-event counts ($I$ is unchanged by a birth, $E(u_i^-)=E(u_i)+1$ at a migration), gives a marked point process. Replacing the random counts by deterministic approximations makes it an inhomogeneous marked Poisson process; reversing time and thinning to the events that change the sample (marks: coalescence, coalescent migration, migration in the sample) leaves a Poisson process of total rate $\frac{\alpha\tilde I}{\tilde E}n_E+\frac{\gamma(\tilde E+1)}{\tilde I}n_I$ whose marks give the stated transition rates.

## Sources

- Isaac H. Goldstein and Julia A. Palacios, "Coalescent Inference for Epidemics with Latent Periods", arXiv (2025): Section 2 (the EI population model, the sampled-genealogy transition probabilities, the marked-point-process likelihood, Theorem 2.1 and its proof), Appendix (comparison of EI and SEIR models and the EI ODE system). <https://doi.org/10.48550/arXiv.2511.09686>
