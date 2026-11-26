# Transition probabilities of time-inhomogeneous substitution under a polyepoch clock

**Setting.** Characters evolve along the branches of a dated phylogeny by an inhomogeneous continuous-time Markov chain (ICTMC) with generator $\mathbf{Q}(t)$. In general the transition matrix over $[t_0, t]$ is the time-ordered (Peano–Baker) series
$$\mathbf{P}(t_0,t) = \mathbf{I} + \int_{t_0}^t\mathbf{Q}(\tau_1)\,d\tau_1 + \int_{t_0}^t\mathbf{Q}(\tau_1)\int_{t_0}^{\tau_1}\mathbf{Q}(\tau_2)\,d\tau_2\,d\tau_1 + \cdots,$$
which has no closed form.

**Proposition (rate-scaled generators).** If $\mathbf{Q}(t)$ commutes with $\int_{t_0}^t\mathbf{Q}(\tau)\,d\tau$ for all $t$, then $\mathbf{P}(t_0,t) = \exp\big(\int_{t_0}^t\mathbf{Q}(\tau)\,d\tau\big)$. This holds for $\mathbf{Q}(t) = f(t)\mathbf{Q}$ with a fixed generator $\mathbf{Q}$ and a positive integrable rate (clock) function $f$, so along a branch from node $\mathrm{pa}(i)$ to node $i$,
$$\mathbf{P}\big(t_{\mathrm{pa}(i)}, t_i\big) = \exp\big(b_i\,\mathbf{Q}\big), \qquad b_i = \int_{\mathrm{branch}\ i} f(t)\,dt,$$
the branch length in expected substitutions per site.

**Polyepoch clock.** Take $f$ piecewise constant on a fine grid $w_0 < w_1 < \cdots$ with value $\theta_m$ on the $m$-th epoch. Then every branch length is a finite sum of epoch rates times the time the branch spends in each epoch,
$$b_i = \sum_m \theta_m\,\big|[w_{m-1}, w_m] \cap \mathrm{branch}_i\big|,$$
which is linear in $\boldsymbol\theta$, so the likelihood and its gradient in $\boldsymbol\theta$ and node times are cheap for hundreds of epochs. A Gaussian Markov random field prior on $\log\boldsymbol\theta$ smooths the rate function over time, and Hamiltonian Monte Carlo samples the joint posterior.

## Depends on

## Expansion

When $\mathbf{Q}(t)$ commutes with its running integral, all terms of the Peano–Baker series reorder into the exponential series of the integral. With $\mathbf{Q}(t) = f(t)\mathbf{Q}$ all generators are multiples of one matrix and commute, so time inhomogeneity only rescales the branch length: the substitution process is the homogeneous chain run on the clock time $\int f$. The piecewise-constant choice makes these clock times exact linear combinations of epoch overlaps; by the chain rule, gradients of the tree likelihood with respect to $\theta_m$ are sums of branch-length gradients weighted by overlap lengths, computable in linear time over the tree.

## Sources

- P. Datta, P. Lemey and M. A. Suchard, "Inhomogeneous continuous-time Markov chains to infer flexible time-varying evolutionary rates", arXiv:2510.11982 (2025), Section 2 (ICTMC transition probabilities, rate-scaled generators and the polyepoch clock branch-length formula), <https://doi.org/10.48550/arXiv.2510.11982>.
