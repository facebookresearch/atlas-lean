# Non-trivial quasi-stationary distribution of the general stochastic epidemic under modified absorption

**Quasi-stationarity.** Let $(X_t)_{t\ge0}$ be a continuous-time Markov chain on a finite set $S' = S \cup \Delta$ that is absorbed in $\Delta$ at time $\tau = \inf\{t : X_t \in \Delta\}$. A probability measure $\nu$ on $S$ is a *quasi-stationary distribution* (QSD) if $\mathbb{P}_\nu(X_t \in A \mid \tau > t) = \nu(A)$ for all $t \ge 0$ and $A \subseteq S$; it is a *quasi-limiting distribution* (Yaglom limit) for an initial law $\mu$ if $\mathbb{P}_\mu(X_t \in A \mid \tau > t) \to \nu(A)$ as $t \to \infty$. Under a QSD the absorption time is exponential: $\mathbb{P}_\nu(\tau > t) = e^{-\lambda(\nu) t}$ for some $\lambda(\nu) \ge 0$.

**Model.** The general (Markovian) stochastic SIR epidemic in a closed population of size $N+1$ is the chain $(S_t, I_t)$ with $S_t + I_t + R_t = N + 1$, started from $(S_0, I_0) = (N, 1)$, with transitions

$$
(s,i) \to (s-1, i+1) \ \text{at rate } \beta s i, \qquad (s,i) \to (s, i-1) \ \text{at rate } \mu i,
$$

where $\beta > 0$ is the infection rate and $\mu > 0$ the removal rate. States with $i = 0$ are absorbing.

**Statement.**

1. *Triviality.* With the natural absorbing set $\{i = 0\}$, the chain is strictly evolutionary (reducible), and its QSD is a point mass on the last transient state before absorption: all quasi-stationary mass sits on a single state, so the QSD carries no information about the epidemic's course.
2. *Modified absorption.* Let $\hat\Xi = \inf\{t > 0 : I_t \ne I_0\}$ be the first jump time and declare the process absorbed at

$$
\tau^* = \inf\{t > \hat\Xi : I_t = 1\},
$$

i.e. on returning to a single infective after leaving the initial state, with transient set $\{(N,1)\} \cup \{(s,i) : i \ge 2\}$. Then there is a non-trivial QSD $\nu_{\mathrm{SIR}}$ for $\tau^*$, positive on every transient state, if and only if

$$
\mu > \beta N .
$$

In that case $\nu_{\mathrm{SIR}}$ is the quasi-limiting distribution of the chain started from $(N,1)$, while for every initial law $\rho$ with $\rho(N,1) = 0$ the conditioned law converges to the point mass at $(0,2)$.

The condition says the removal rate must exceed the total initial infection pressure, so in this framework a non-trivial QSD exists only for strongly subcritical epidemics; the ratio-of-expectations distribution is the more useful long-term descriptor otherwise.

## Depends on

- [Almost-sure existence of the SIR chain](../../stochastic-sir-epidemic-and-its-law-of-large-num/ae-is-chain-path-sir.md)

## Proof sketch

For a reducible chain whose generator restricted to $S$ has leading eigenvalue $-\lambda$ of geometric multiplicity one, there is a unique QSD from which the communicating class $S_{a(\lambda)}$ attaining $\lambda$ is accessible; it solves $\nu Q = -\lambda\nu$ and is also the Yaglom limit for initial laws from which $S_{a(\lambda)}$ is accessible (van Doorn and Pollett). Since the SIR chain only moves by $(-1,+1)$ and $(0,-1)$, every state is its own class, and the eigenvalues of the restricted generator are minus the total exit rates $i(\beta s + \mu)$. The leading eigenvalue is attained at the state with the smallest exit rate, which with natural absorption is a state just before extinction; this gives the point mass. Under modified absorption one wants the leading eigenvalue to belong to $(N,1)$, the class accessing all others, with exit rate $\beta N + \mu$. The smallest competing exit rate among states with $i \ge 2$ is $2\mu$, attained at $(0,2)$, so $(N,1)$ dominates exactly when $2\mu > \beta N + \mu$, i.e. $\mu > \beta N$. The QSD is then explicit as a sum over lattice paths from $(N,1)$ of products of ratios $\rho_j/(\lambda_j - \lambda_0)$ of transition rates to exit-rate gaps, obtained from the asymptotics of sums of independent exponential holding times; the same construction gives explicit non-trivial QSDs for the Maki–Thompson and Daley–Kendall rumor models, which differ from SIR in that removal is caused by spreader encounters rather than independent recovery.

## Sources

- Iddo Ben-Ari, Elcio Lebensztayn and Lucas Sousa Santos, "On quasi-stationary distributions for stochastic rumor models", *Chaos, Solitons & Fractals* 212 (2026), 119146, <https://doi.org/10.1016/j.chaos.2026.119146>. Preprint version: arXiv:2511.23390 (2025), Definitions 3.1–3.2 and Theorem 3.3 (QSD background), Theorems 4.1, 4.2 and 4.6 (Maki–Thompson model) and Theorem 5.2 (SIR model), <https://doi.org/10.48550/arXiv.2511.23390>.
