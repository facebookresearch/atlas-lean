# Decay-rate bound for networked SIS with phase-type transmission and recovery times

**Setting.** On an undirected graph $\mathcal G$ with $n$ nodes and adjacency matrix $A$, each node is susceptible or infected. In the **generalized networked SIS model** an infected node $i$ recovers after a random recovery time and, while infected, attempts to infect each neighbour $j$ at the successive times of a renewal process with i.i.d. inter-attempt (transmission) times; attempts on infected neighbours have no effect. Transmission and recovery times follow **phase-type distributions** $(\phi, T)$ with $p$ transient phases and $(\psi, R)$ with $q$ transient phases (Assumption 3.4): absorption times of Markov chains with transient generator $T$ (resp. $R$), initial law $\phi$ (resp. $\psi$) and exit-rate vector $b = -T\mathbf 1_p$. The **exponential decay rate** is

$$\lambda = -\sup_{\mathcal V_0 \subseteq [n]}\ \limsup_{t\to\infty}\frac1t \log\sum_{i=1}^n \mathbb E[z_i(t)],$$

where $z_i(t) \in \{0,1\}$ is the infection indicator of node $i$ and $\mathcal V_0$ the initially infected set.

**Theorem (Theorem 5.2).** Let

$$\mathcal A = (\phi b^\top) \otimes A \otimes (\psi\mathbf 1_q^\top) + I_{np} \otimes R^\top + (T^\top + \phi b^\top) \otimes I_{nq} \in \mathbb R^{npq \times npq}.$$

Then $\lambda \ge -\eta(\mathcal A)$, where $\eta(\mathcal A)$ is the spectral abscissa (largest real part of an eigenvalue). In particular, the infection dies out exponentially fast in expectation whenever $\eta(\mathcal A) < 0$. If transmission times are exponential with rate $\beta$ (Corollary 5.3), the bound becomes $\lambda \ge -\eta\big(\beta A \otimes (\psi\mathbf 1_q^\top) + I_n \otimes R^\top\big)$, and for exponential recovery with rate $\delta$ as well it reduces to the classical Markovian condition $\eta(\beta A - \delta I) < 0$.

The exact decay rate is $\lambda = -r$, where $r$ is the largest real part of the non-zero eigenvalues of the generator of an exact Markov representation on $\prod_i(1 + p^{|\mathcal N_i|}q)$ states (Proposition 5.1, Corollary 4.6); the theorem replaces this exponentially large matrix by one of size $npq$.

## Expansion

Phase-type clocks turn the non-Markovian process into a Markov one: each directed edge carries a vector $x^{ji} \in \{0, e_1, \ldots, e_p\}$ recording the current phase of its transmission clock, and each node a vector $y^i \in \{0, f_1, \ldots, f_q\}$ recording the phase of its recovery clock, all driven by Poisson counters (Theorem 4.3). Taking expectations of the resulting stochastic differential equations gives a linear system for the first moments that is closed after replacing the nonlinear "susceptible" factor $1 - \mathbf 1^\top y^i$ by its upper bound $1$; this gives a positive linear comparison system with matrix $\mathcal A$, whose spectral abscissa bounds the growth of the expected number of infected nodes. The three terms of $\mathcal A$ are, in order, new transmissions along edges that restart both clocks, the progression of recovery phases, and the progression and renewal of transmission phases. The bound shows that the shape of the transmission and recovery time distributions, not just their means, governs whether an outbreak dies out.

## Sources

- Masaki Ogura and Victor M. Preciado, "Stability of SIS spreading processes in networks with non-Markovian transmission and recovery", arXiv:1606.08518 (2016), Definitions 3.1 and 3.3, Assumption 3.4, Theorem 4.3, Corollary 4.6, Proposition 5.1, Theorem 5.2 and Corollary 5.3, <https://doi.org/10.48550/arXiv.1606.08518>. Published version: IEEE Transactions on Control of Network Systems 7 (2020) 349–359, <https://doi.org/10.1109/TCNS.2019.2905131>.
