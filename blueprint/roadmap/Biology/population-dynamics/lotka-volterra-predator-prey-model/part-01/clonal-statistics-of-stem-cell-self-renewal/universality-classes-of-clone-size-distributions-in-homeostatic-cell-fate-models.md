# Universality classes of clone size distributions in homeostatic cell fate models

**Generic cell fate model.** Cells occupy states $X_1,\dots,X_m$ and evolve as a continuous-time multi-type branching process with

$$X_i \xrightarrow{\lambda_i r_{ijk}} X_j + X_k, \qquad X_i \xrightarrow{\omega_{ij}} X_j, \qquad X_i \xrightarrow{\gamma_i} \emptyset ,$$

(division with outcome probabilities $r_{ijk}$, state change, loss). With $r_{ij} = \sum_k (r_{ijk} + r_{ikj})/2$, the mean numbers $\bar n = (\bar n_i)$ satisfy $\dot{\bar n} = A\bar n$ with off-diagonal entries $\kappa_{ji} = 2\lambda_j r_{ji} + \omega_{ji} \ge 0$ (rate of $X_j \to X_i$ transitions) and diagonal entries $\kappa_{ii} - \delta_i$, where $\delta_i = \lambda_i + \sum_j \omega_{ij} + \gamma_i$. $A$ is cooperative (Metzler).

**Homeostasis and compartments.** View $A$ as the weighted adjacency matrix of the cell-state graph and decompose it into strongly connected components (SCCs); by Perron–Frobenius each SCC has a real dominant eigenvalue $\mu_k$. A non-trivial Lyapunov-stable steady state exists iff every SCC at the apex of a lineage has $\mu_k = 0$ and every SCC downstream of it has $\mu_k < 0$. The apex SCC is the **renewing compartment** $\mathcal{R}$; the downstream SCCs form the **committed compartment** $\mathcal{C}$.

**Two classes.** A model is **generalized invariant asymmetry (GIA)** if every division in $\mathcal{R}$ is of type $R \to R + C$, so the number of renewing cells per clone is conserved; otherwise (some $R \to R+R$ or $R \to C+C$ divisions) it is **generalized population asymmetry (GPA)** and no conservation law holds. Let $\bar n_s$ be the mean size of surviving clones.

**GIA Markovian test case.** For $X_1 \xrightarrow{\lambda_1} X_1 + X_2$, $X_2 \xrightarrow{\lambda_2} 2X_2$, $X_2 \xrightarrow{\gamma} \emptyset$ with $\lambda_2 < \gamma$, the clone keeps one $X_1$ cell, the stationary mean is $\bar n_2 = \lambda_1/(\gamma - \lambda_2)$, and for large $\bar n_2$ the rescaled size $x_2 = n_2/\bar n_2$ has density

$$P(x_2) = \frac{(1-\hat\lambda_2)^{\hat\lambda_1/\hat\lambda_2}\,\hat\lambda_2^{\hat\lambda_1 x_2/(1-\hat\lambda_2)}\,\Gamma\!\left(\frac{\hat\lambda_1}{\hat\lambda_2} + \frac{\hat\lambda_1 x_2}{1-\hat\lambda_2}\right)}{x_2\,\Gamma\!\left(\frac{\hat\lambda_1}{\hat\lambda_2}\right)\Gamma\!\left(\frac{\hat\lambda_1 x_2}{1-\hat\lambda_2}\right)}, \qquad \hat\lambda_i = \lambda_i/\gamma,$$

which is peaked for large $\hat\lambda_1$, tends to an exponential as $\hat\lambda_1, \hat\lambda_2 \to 1$, and tends to a normal distribution with unit mean and variance $1/\hat\lambda_1$ as $\hat\lambda_1 \to \infty$.

**GPA Markovian approximation.** For $X_1 \xrightarrow{\lambda_1} 2X_1$, $X_1 + X_2$ or $2X_2$ with probabilities $r_1$, $1 - r_1 - r_2$ and $r_2$, $X_1 \xrightarrow{\omega} X_2$, $X_2 \xrightarrow{\lambda_2} 2X_2$ and $X_2 \xrightarrow{\gamma} \emptyset$, with $\lambda_1 r_1 = \lambda_1 r_2 + \omega$ and $\lambda_2 < \gamma$ (homeostasis), $n_1$ is a critical binary branching process, so the number of $X_1$ cells in surviving clones is asymptotically exponential with mean $\bar n_{1,s} \simeq \lambda_1 r_1 t$, and the rescaled total clone size $n/\bar n_s$ converges to the standard exponential distribution as $t \to \infty$ (Eqs. (12)–(13)).

**Universality (the source's argument, not part of the statement).** The source argues, by Markovian approximation of generic compartment dynamics and by stochastic simulations of random networks of both classes, that the two Markovian results above are universal ("we reason that all GPA models are expected to generate Exponential clone size distributions for large times"):

- *GPA:* clones go extinct while the tissue stays stationary, so $\bar n_s$ grows without bound (linearly in $t$), and the rescaled clone size $n/\bar n_s$ is expected to converge to the standard exponential distribution for any GPA network.
- *GIA:* $\bar n_s$ saturates; with effective renewal rate $\hat\lambda_R = \lambda_R/\gamma_C$ (division and loss rates averaged over the stationary state occupancies of $\mathcal{R}$ and $\mathcal{C}$), the rescaled clone size is expected to tend to a normal distribution as $\hat\lambda_R \to \infty$, provided transitions inside $\mathcal{R}$ are fast compared with loss from $\mathcal{C}$; with slow transitions between renewing states of different division rates the distribution can be bimodal.

On this argument, clone size statistics in these limits identify only the class (conserved or non-conserved renewing compartment), not the underlying self-renewal mechanism.

## Expansion

In the GPA Markov approximation, $X_1 \to 2X_1$ with probability $r_1$, $X_1 \to X_1 + X_2$, $X_1 \to 2X_2$ with probability $r_2$, and $X_1 \to X_2$ at rate $\omega$, homeostasis requires $\lambda_1 r_1 = \lambda_1 r_2 + \omega$, making $n_1$ a critical birth–death process; the surviving clone size of a critical birth–death process is asymptotically exponential with mean $\simeq \lambda_1 r_1 t$. Committed cells produced at a rate proportional to $n_1$ have Poisson-like fluctuations, mean equal to variance and of order $t$, so their rescaled spread vanishes like $t^{-1/2}$ and the total rescaled clone size inherits the exponential law. For GIA models the single conserved renewing cell feeds the committed compartment like an immigration source; at high production rates the committed number concentrates and becomes approximately normal. Generic, non-Markovian compartment dynamics are argued to share these limits by central-limit reasoning, and stochastic simulations of large random networks of both classes confirm the collapse.

## Sources

- C. Parigini, P. Greulich, "Universality of clonal dynamics poses fundamental limits to identify stem cell self-renewal strategies", eLife 9 (2020) e56532, Equations (3)–(13) and the Results sections on model generalization, Markovian approximation and universality, <https://doi.org/10.7554/elife.56532>, PMCID PMC7444910.
