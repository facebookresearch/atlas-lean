# Mean reproductive matrix of infectious units and R0 in structured populations

**Setting.** A Markovian $SIR$ or $SIS$ epidemic spreads in a large population whose individuals are grouped into local units (households, couples, neighborhoods on a circle; static or dynamic). A unit containing at least one infective is an *infectious unit*, and it is in one of $K$ states (e.g. number of susceptibles and infectives it contains). In the early phase an infective experiences three kinds of events: *global infections* (contacts with uniformly chosen, almost surely susceptible individuals, who start new infectious units), *local transitions* (within-unit infection, partnership formation or dissolution, which move the infective to another state) and *recovery*. Classify each infective by the state of its unit when it becomes infected or changes state.

**Construction.** For an infective currently in state $i$, let $p_{ij}$ be the probability that it next moves to a state-$j$ unit (with $1-\sum_jp_{ij}$ the probability of recovering first) and $\phi_{ij}$ the mean number of new state-$j$ infectives created before it leaves state $i$. With $\mathbf P=(p_{ij})$ and $\Phi=(\phi_{ij})$, the mean reproductive matrix $\mathbf M$, whose entry $M_{ij}$ is the expected number of state-$j$ infectives produced over the whole infectious period of an infective starting in state $i$, satisfies $\mathbf M=\Phi+\mathbf P\mathbf M$, hence

$$\mathbf M=(\mathbf I-\mathbf P)^{-1}\Phi=\Bigl(\sum_{n\ge0}\mathbf P^n\Bigr)\Phi ,$$

and $R_0=\rho(\mathbf M)$, its Perron root, equivalently $R_0=\lim_n\mathbb E[X_n]^{1/n}$ for the generation sizes $X_n$ of the multitype branching approximation. $\mathbf P$, $\Phi$ may be computed event by event or by integrating over sojourns; both give the same $\mathbf M$.

**Results.**

1. *(Households.)* For the household SIR model the construction gives a matrix whose largest eigenvalue coincides with the household-based $R_0$ of earlier work, although the types are infectious-unit states rather than generations within households.
2. *(Great circle model.)* With global contact rate $\lambda_G$, neighbor contact rate $\lambda_L$ and recovery rate $\gamma$, write $\mu_G=\lambda_G/\gamma$ and $p_L=\lambda_L/(\lambda_L+\gamma)$. Then $R_0$ solves $s^2-(\mu_G+p_L)s-\mu_Gp_L=0$:

$$R_0=\frac{p_L+\mu_G+\sqrt{(p_L+\mu_G)^2+4p_L\mu_G}}{2},$$

and $R_0\gtrless1$ exactly when the clump threshold $R_*=\mu_G(1+p_L)/(1-p_L)\gtrless1$.
3. *(SIS sexually transmitted infection with dynamic partnerships.)* With single individuals forming partnerships at rate $\alpha\sigma$ ($\sigma$ the steady-state fraction single, $\sigma=(-\delta+\sqrt{\delta^2+4\delta\alpha})/(2\alpha)$), dissolution rate $\delta$, within-partnership transmission rate $\beta$, recovery rate $\gamma$ and no casual contacts, only infections within partnerships occur and

$$R_0=\frac{\beta\{\alpha\sigma(\delta+\gamma)+\gamma^2\}}{\gamma(\alpha\sigma+\delta+\gamma)(\beta+\delta+2\gamma)},$$

the mean number of partners an infective infects during its infectious period. With casual contacts, $R_0$ is the largest root of a cubic.

## Expansion

Conditioning on the first event that changes an infective's unit state gives the renewal identity $\mathbf M=\Phi+\mathbf P\mathbf M$; since recovery has positive probability from every state, $\mathbf P$ is substochastic with spectral radius below one and the Neumann series converges. Each infection starts a new infectious unit of a definite type, so the early epidemic is a multitype Galton–Watson process with mean matrix $\mathbf M$, and $R_0>1$ is the supercriticality condition. Equivalence with other threshold parameters (household or clump reproduction numbers) follows because they are obtained by aggregating generations of the same branching process, which preserves the side of one on which the Perron root lies.

## Sources

- Peter Neal, Thitiya Theparod, "The basic reproduction number, R0, in structured populations", Mathematical Biosciences 315 (2019), 108224, <https://doi.org/10.1016/j.mbs.2019.108224>. Published version of arXiv:1903.10353, cited next; locators there refer to the arXiv version.
- P. Neal, T. Theparod, "The basic reproduction number, $R_0$, in structured populations", arXiv:1903.10353 (2019), model setup and construction of $\mathbf M$ (equations for $\mathbf M=\Phi+\mathbf P\mathbf M$), the household example with Lemmas 1–2, the sexually transmitted disease example and the great circle example. <https://doi.org/10.48550/arXiv.1903.10353>
