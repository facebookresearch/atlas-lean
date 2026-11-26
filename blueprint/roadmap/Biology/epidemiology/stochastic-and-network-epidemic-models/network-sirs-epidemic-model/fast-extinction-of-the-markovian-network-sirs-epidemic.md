# Fast extinction of the Markovian network SIRS epidemic

**Model.** Individuals are the nodes of a connected undirected graph $G$ on $N$ nodes with symmetric adjacency matrix $A$ and spectral radius $\lambda_1(A)$. Each node is in state $S$, $I$ or $R$; as a continuous-time Markov chain on $\{S,I,R\}^N$, a susceptible node is infected at rate $\beta\sum_ja_{ij}\mathbf 1\{X_j=I\}$, an infected node recovers at rate $\delta$, a recovered node loses immunity at rate $\gamma$, and (optionally) a susceptible node is vaccinated, moving to $R$, at rate $\sigma\ge 0$. All infection-free configurations form a closed class, which the chain enters in finite time almost surely. Write $\tau=\beta/\delta$.

**Proposition (persistence bound).** With $\sigma=0$, for every initial configuration and all $t\ge 0$,

$$\mathbb P\Big(\sum_i\mathbf 1\{X_i(t)=I\}>0\Big)\le\sqrt{N\sum_i\mathbf 1\{X_i(0)=I\}}\;e^{(\beta\lambda_1(A)-\delta)t}.$$

**Corollary (mean extinction time).** Let $\tau^{FS}$ be the hitting time of the infection-free set. If $\beta/\delta<1/\lambda_1(A)$, then

$$\mathbb E\,\tau^{FS}\le\frac{\log N+1}{\delta-\beta\lambda_1(A)} .$$

Hence along a graph sequence with $\delta-\beta\lambda_1(A_N)\ge c>0$ (for instance $k$-regular graphs, where $\lambda_1=k$), the infection dies out in time $O(\log N)$ in expectation.

**Proposition (absorption in the all-susceptible state).** If moreover $-\gamma$ is not an eigenvalue of $\beta A-\delta I$, there is a constant $C=C(A,\beta,\delta,\gamma)>0$ with

$$\mathbb P\big(Y(t)\ne(S,\dots,S)\big)\le C\sqrt{N\sum_i\mathbf 1\{X_i(0)\in\{I,R\}\}}\;e^{\max\{\beta\lambda_1(A)-\delta,\,-\gamma\}\,t}.$$

## Expansion

The marginal infection probabilities $P_i(t)=\mathbb P(X_i(t)=I)$ satisfy an exact equation whose pair-correlation terms enter with a minus sign, so $\dot P\le(\beta A-\delta I)P$ componentwise; since $\beta A-\delta I$ is Metzler, $P(t)\le e^{t(\beta A-\delta I)}P(0)$. A union bound gives $\mathbb P(\text{some }I)\le\mathbf 1^{\mathsf T}P(t)$, and Cauchy–Schwarz with symmetric $A$ gives the $\sqrt N\,\|P(0)\|_2$ factor. Integrating $\min\{1,Ne^{-(\delta-\beta\lambda_1)t}\}$ and splitting at $t^\ast=\log N/(\delta-\beta\lambda_1)$ gives the mean-time bound. The temporary immunity class adds the rate $-\gamma$ to the decay of the probability of not being fully susceptible. This is the SIRS analogue of the fast die-out bound on the expected extinction time of network SIS epidemics.

## Depends on

- [Fast die-out, expected extinction time](../../sis-extinction-times-on-finite-graphs/lintegral-extinction-time-le.md)

## Sources

- Stefania Ottaviano and Stefano Bonaccorsi, "Some aspects of the Markovian SIRS epidemic on networks and its mean-field approximation", arXiv:1912.11287 (2019), Section 2 (The Exact Model), proposition bounding the persistence probability, its corollary on the mean hitting time of the final set, and the proposition on the time to the absorbing state, <https://doi.org/10.48550/arXiv.1912.11287>.
