# Conditional age given the phase under Poisson observation

Model an individual's life as a continuous-time Markov chain on transient phases $\{1,\dots,m\}$ and one absorbing state $0$ (death). Let $\mathbf{Q}$ be the $m \times m$ sub-generator on the transient phases (nonsingular, so $(-\mathbf{Q})^{-1} \ge 0$ exists), $\boldsymbol\alpha$ the initial phase distribution at birth, $\mathbf{e}_j$ the $j$-th unit column vector, and $\lambda_j = -Q_{jj}$. The lifetime $L$ is phase-type $\mathrm{PH}(\boldsymbol\alpha,\mathbf{Q})$.

**Stationary population with Poisson births.** If births occur at the epochs of a Poisson process on $(-\infty,0)$ and an individual is sampled at time $0$ and found in phase $j$, its age $A$ satisfies

$$

F_j(s) := \mathbb{P}[A \le s \mid \text{phase } j] = 1 - \frac{\boldsymbol\alpha\, e^{\mathbf{Q}s}(-\mathbf{Q})^{-1}\mathbf{e}_j}{\boldsymbol\alpha(-\mathbf{Q})^{-1}\mathbf{e}_j}, \qquad s \ge 0,

$$

independently of the birth rate (the age of a customer in an $M/PH/\infty$ queue in steady state).

**Proposition (Poisson observation).** Follow one individual from birth and observe its phase at the first event $A_o$ of an independent Poisson process of rate $\gamma$, conditional on the individual being alive then, in phase $\varphi_o = j$. With $\mathbf{T} = \mathbf{Q} - \gamma\mathbf{I}$,

$$

\mathbb{P}[A_o \le s \mid \varphi_o = j] = 1 - \frac{\boldsymbol\alpha\, e^{\mathbf{T}s}(-\mathbf{T})^{-1}\mathbf{e}_j}{\boldsymbol\alpha(-\mathbf{T})^{-1}\mathbf{e}_j}, \qquad s \ge 0 .

$$

Write $A_o = Y_j + Z_j$, where $Z_j$ is the time already spent in phase $j$ at the observation and $Y_j = A_o - Z_j$ is the age at which the individual last entered phase $j$. Given $\varphi_o = j$, $Z_j$ is exponential with rate $\gamma + \lambda_j$, and $Y_j$ has an atom at $0$ (born in phase $j$ and never left it) of mass $\alpha_j / \big((\lambda_j+\gamma)\,\boldsymbol\alpha(-\mathbf{T})^{-1}\mathbf{e}_j\big)$.

Successive observations at Poisson epochs give analogous block-matrix-exponential formulas for the age at the $k$-th observation given the observed phase sequence.

## Expansion

The probability of being in phase $j$ at age $s$ is $\boldsymbol\alpha e^{\mathbf{Q}s}\mathbf{e}_j$. For Poisson births the density of the age of an individual found in phase $j$ is proportional to this, and integrating gives $F_j$. Under Poisson observation, the observation happens at age $s$ with density $\gamma e^{-\gamma s}$, so the joint density of age $s$ and phase $j$ is $\gamma\,\boldsymbol\alpha e^{(\mathbf{Q}-\gamma\mathbf{I})s}\mathbf{e}_j$; normalizing over $s$ gives the formula with $\mathbf{T}$. The exponential law of $Z_j$ comes from the race, started at the last entry into phase $j$, between leaving phase $j$ (rate $\lambda_j$) and the observation (rate $\gamma$): the joint density of $(Y_j, Z_j)$ factorizes, with factor $e^{-(\lambda_j+\gamma)z}$ in $Z_j$.

## Sources

- Sophie Hautphenne, Melanie Massaro, Peter Taylor, "How old is this bird? The age distribution under some phase sampling schemes", arXiv (2015); Journal of Mathematical Biology (2017). Section 3 (equation for $F_j$), Section 4 (Propositions 4.1–4.3 and 4.5). <https://doi.org/10.48550/arXiv.1504.03527>. Published version: Journal of Mathematical Biology 75(6-7) (2017), 1319–1347, <https://doi.org/10.1007/s00285-017-1121-x>; locators above refer to the arXiv version.
