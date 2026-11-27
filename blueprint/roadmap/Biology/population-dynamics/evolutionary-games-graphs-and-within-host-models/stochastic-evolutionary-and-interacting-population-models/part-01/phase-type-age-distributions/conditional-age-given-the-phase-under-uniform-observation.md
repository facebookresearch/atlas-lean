# Conditional age given the phase under uniform observation and the rare-observation limit

Let an individual's lifetime be $\mathrm{PH}(\boldsymbol\alpha,\mathbf{Q})$: an absorbing continuous-time Markov chain with transient phases $\{1,\dots,m\}$, sub-generator $\mathbf{Q}$, initial distribution $\boldsymbol\alpha$, and $\lambda_j = -Q_{jj}$.

**Proposition (uniform observation).** Suppose the phase is observed once, at a time $A_o$ uniformly distributed on $[0,t]$ after birth, and the individual is alive then, in phase $\varphi_o = j$. Then for $0 \le s \le t$

$$

\mathbb{P}[A_o \le s \mid \varphi_o = j] = 1 - \frac{\boldsymbol\alpha\,\big[e^{\mathbf{Q}s} - e^{\mathbf{Q}t}\big]\,(-\mathbf{Q})^{-1}\mathbf{e}_j}{\boldsymbol\alpha\,\big[\mathbf{I} - e^{\mathbf{Q}t}\big]\,(-\mathbf{Q})^{-1}\mathbf{e}_j},

$$

and the probability is $1$ for $s > t$. Writing $A_o = Y_j + Z_j$, with $Z_j$ the time already spent in phase $j$ at the observation and $Y_j = A_o - Z_j$ the age at which the individual last entered phase $j$, $Z_j$ satisfies, for $z \le t$,

$$

\mathbb{P}[Z_j \le z \mid \varphi_o = j] = 1 - \frac{\boldsymbol\alpha\,\big[\mathbf{I} - e^{\mathbf{Q}(t-z)}\big]\,(-\mathbf{Q})^{-1}\mathbf{e}_j\; e^{-\lambda_j z}}{\boldsymbol\alpha\,\big[\mathbf{I} - e^{\mathbf{Q}t}\big]\,(-\mathbf{Q})^{-1}\mathbf{e}_j}.

$$

**Corollary (rare-observation limit).** Letting the Poisson observation rate $\gamma \to 0$ (equivalently $t \to \infty$ in the uniform scheme), the conditional age distribution given phase $j$ converges to

$$

\mathbb{P}[A_o \le s \mid \varphi_o = j] = 1 - \frac{\boldsymbol\alpha\,e^{\mathbf{Q}s}(-\mathbf{Q})^{-1}\mathbf{e}_j}{\boldsymbol\alpha(-\mathbf{Q})^{-1}\mathbf{e}_j} = F_j(s),

$$

the age distribution of an individual found in phase $j$ in a stationary population with Poisson births; the time $Z_j$ already spent in phase $j$ at the observation becomes exponential with rate $\lambda_j$.

So the answer to "how old is an individual in phase $j$" depends on the observation scheme, and the stationary-population answer is the limit of rare observation.

## Expansion

Under uniform observation the joint density of observation age $s \in [0,t]$ and phase $j$ is $t^{-1}\boldsymbol\alpha e^{\mathbf{Q}s}\mathbf{e}_j$; integrating with $\int_s^t e^{\mathbf{Q}u}du = (e^{\mathbf{Q}s}-e^{\mathbf{Q}t})(-\mathbf{Q})^{-1}$ gives the formula. The rare-observation limit sends $e^{\mathbf{Q}t} \to 0$, since $\mathbf{Q}$ is a transient sub-generator. These formulas were applied to reconstruct the age pyramid of the Chatham Island black robin during intensive conservation management.

## Sources

- Sophie Hautphenne, Melanie Massaro, Peter Taylor, "How old is this bird? The age distribution under some phase sampling schemes", arXiv (2015); Journal of Mathematical Biology (2017). Section 5 (Propositions 5.1–5.3), Section 6 (Corollaries 6.1–6.3). <https://doi.org/10.48550/arXiv.1504.03527>. Published version: Journal of Mathematical Biology 75(6-7) (2017), 1319–1347, <https://doi.org/10.1007/s00285-017-1121-x>; locators above refer to the arXiv version.
