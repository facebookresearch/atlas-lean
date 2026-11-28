# Poisson mRNA number across a cell cycle with gene replication

**Model.** Follow one cell lineage through periodic cell cycles of deterministic length $\tau_D$; let $s \in [0, \tau_D)$ be the time since the last division.

- *Transcription:* mRNAs are produced at rate $\lambda_1$ before gene replication and at rate $2\lambda_1$ after it.
- *Replication:* the gene is duplicated at the deterministic time $s = \tau_R$, with $0 < \tau_R < \tau_D$.
- *Degradation:* each mRNA is degraded independently at rate $\sigma_1$.
- *Translation:* each mRNA produces proteins at rate $\lambda_2$; proteins do not degrade.
- *Division:* at $s = \tau_D$ each molecule independently goes to the followed daughter cell with probability $1/2$ (binomial partitioning), and the transcription rate resets to $\lambda_1$.

Let $M_s$ and $P_s$ be the mRNA and protein numbers at cell-cycle time $s$, once the lineage has reached its periodic equilibrium (after many divisions).

**Proposition.** At equilibrium, $M_s$ is Poisson with mean

$$x_s = \frac{\lambda_1}{\sigma_1}\left[1 - \frac{e^{-(s + \tau_D - \tau_R)\sigma_1}}{2 - e^{-\tau_D \sigma_1}} + \mathbb{1}_{\{s \ge \tau_R\}}\big(1 - e^{-(s - \tau_R)\sigma_1}\big)\right], \qquad 0 \le s < \tau_D .$$

**Proposition (protein mean before replication).** For $s \in [0, \tau_R)$,

$$\mathbb{E}[P_s] = \mathbb{E}[P_0] + \lambda_2\Big[\frac{\lambda_1}{\sigma_1}s + \Big(x_0 - \frac{\lambda_1}{\sigma_1}\Big)\frac{1 - e^{-\sigma_1 s}}{\sigma_1}\Big],$$

and $\mathrm{Var}(P_s)$ is an explicit affine function of $\mathrm{Var}(P_0)$, $\mathrm{Cov}(P_0, M_0)$ and $x_0$.

## Proof sketch

Poisson laws are preserved by every step of the cycle: an immigration–death process started from a Poisson number stays Poisson, with mean solving $\dot x = \lambda(s) - \sigma_1 x$; independent binomial thinning with probability $1/2$ maps $\mathrm{Poisson}(x)$ to $\mathrm{Poisson}(x/2)$. The equilibrium is therefore Poisson with a mean that is periodic in $s$, and the fixed point of the one-cycle map $x_0 \mapsto \frac12 x_{\tau_D^-}$ gives the factor $2 - e^{-\tau_D\sigma_1}$. Protein moments follow by integrating the linear moment equations driven by $M_s$: $\frac{d}{ds}\mathbb E[P_s]=\lambda_2\,\mathbb E[M_s]$ with $\mathbb E[M_s]=\frac{\lambda_1}{\sigma_1}+\big(x_0-\frac{\lambda_1}{\sigma_1}\big)e^{-\sigma_1 s}$ for $s<\tau_R$, so both terms of the protein mean carry the factor $\lambda_2$ (the source's Proposition 4.2 omits it on the second term; its variance formula carries it).

## Sources

- Bertrand Cloez, Renaud Dessalles, Alexandre Genadot, Florent Malrieu, Aline Marguet and Romain Yvinec, "Probabilistic and Piecewise Deterministic models in Biology", *ESAIM: Proceedings and Surveys* 60 (2017), 225–245, <https://doi.org/10.1051/proc/201760225>. Preprint version: arXiv:1706.09163 (2017), section on stochastic models of protein production with cell division and gene replication (Section 4), Propositions 4.1 and 4.2, <https://doi.org/10.48550/arXiv.1706.09163>.
