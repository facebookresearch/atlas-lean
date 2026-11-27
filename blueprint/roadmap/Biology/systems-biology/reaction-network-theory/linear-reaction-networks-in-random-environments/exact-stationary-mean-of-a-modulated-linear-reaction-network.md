# Exact stationary mean of a modulated linear reaction network

**Setting.** Let $Z$ be a stationary, irreducible continuous-time Markov chain on a countable set $\mathcal Z$ with generator $\Lambda$ (entry $\Lambda(z',z)$ is the rate from $z$ to $z'$), stationary distribution $\pi$ ($\Lambda\pi = 0$) and exit rates $\Lambda_0(z) = -\Lambda(z,z) = \sum_{z'\ne z}\Lambda(z',z)$. A reaction network $X$ on $\mathbb{N}^d$ has propensities that are affine in $x$ given the environment, $f(x\mid z) = \Gamma(z)x + \gamma(z)$; with stoichiometric matrix $\mathcal N$ write $A(z) = -\mathcal N\Gamma(z)$ and $b(z) = \mathcal N\gamma(z)$, so that conditional on the environment $\frac{d}{dt}E[X_t] = b(Z_t) - A(Z_t)E[X_t]$ path-wise. Assume every $A(z)$ has only eigenvalues with non-negative real part, and the joint process is ergodic.

**Proposition (embedded chain).** With $\tau_n$ the jump times of $Z$, the embedded chain $W_n = Z(\tau_n)$ has the unnormalized stationary distribution $\tilde\pi(z) = \pi(z)\Lambda_0(z)$.

**Theorem (exact stationary mean, ESME).** Let $x(z)$ be the stationary mean of $X$ at the end of a sojourn of the environment in state $z$, i.e. $x(z) = E[\tilde Y_{2} \mid \tilde Z_1 = z]$ for the stationary version of the chain $(E[X(\tau_n)\mid Z_{[0,\tau_n]}], Z(\tau_n))_n$. Then the $x(z)$ solve the linear system

$$A(z)\,x(z) = \sum_{z'\in\mathcal Z}\Lambda(z,z')\frac{\pi(z')}{\pi(z)}\,x(z') + b(z), \qquad z \in \mathcal Z,$$

which reduces to $A(z)x(z) = (\Lambda^{\top}x)(z) + b(z)$ under detailed balance, and the stationary mean of the network is

$$E[X_\infty] = \sum_{z\in\mathcal Z}\pi(z)\,x(z).$$

In block form, with $\mathcal A = \operatorname{diag}(A(z))$, $\mathcal B = \operatorname{diag}(b(z))$ and $e$ the all-ones vector,

$$E[X_\infty] = (e^{\top}\otimes I_d)\,(\mathcal A - \Lambda\otimes I_d)^{-1}\,\mathcal B\,\pi .$$

When only zero-order rates are modulated ($A(z) \equiv A$), $E[X_\infty] = A^{-1}E_\pi[b(Z)]$ coincides with the averaged-rate (quasi-steady-state) prediction $\bar A^{-1}\bar b$; when first-order rates are modulated the two generally differ, so environmental randomness is visible already in the stationary mean.

## Expansion

By the ergodic theorem, $E[X_\infty]$ is the long-run time average of $X$, which can be split over the sojourn intervals $[\tau_n, \tau_{n+1})$ of the environment. Within a sojourn in state $z$ the conditional mean $Y(t) = E[X(t)\mid Z_{[0,t]}]$ solves the linear ODE $\dot Y = b(z) - A(z)Y$, and the sojourn length is exponential with rate $\Lambda_0(z)$; integrating against this exponential law (using $E[e^{-AT}] = \mu(\mu I + A)^{-1}$ for $T \sim \mathrm{Exp}(\mu)$, valid because the eigenvalues of $A$ have non-negative real part) expresses the expected end value and time integral of $Y$ over a sojourn linearly in the start value. Stationarity of the embedded chain with weights $\tilde\pi = \pi\Lambda_0$ turns these into the linear recursion for $x(z)$, and reweighting each state's time integral by its stationary sojourn frequency gives the sum $\sum_z\pi(z)x(z)$. For $d = 1$ the block formula becomes $e^\top(\mathcal A - \Lambda)^{-1}\mathcal B\pi$, matching a queueing-theory result of O'Cinneide and Purdue (1986, Theorem 3.1).

## Sources

- M. Sinzger-D'Angelo, S. Startceva, H. Koeppl, "Bye bye, linearity, bye: quantification of the mean for linear CRNs in a random environment", Journal of Mathematical Biology (2023), Eqs. (2)–(6), (10)–(16), Definitions 1–2, Propositions 1–2, Theorem 3, Remarks 1–2 and Lemma 4, <https://doi.org/10.1007/s00285-023-01973-x>, PMCID PMC10423146.
