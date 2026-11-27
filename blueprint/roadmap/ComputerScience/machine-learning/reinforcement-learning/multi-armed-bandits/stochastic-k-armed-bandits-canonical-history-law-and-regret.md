# Stochastic k-armed bandits: canonical history law and regret

Fix $k \ge 1$ arms and a horizon $n \ge 1$. A stochastic $k$-armed bandit is a tuple
$\nu = (P_1, \dots, P_k)$ of probability distributions on $\mathbb{R}$ with finite first moments, with means
$\mu_i$ and $\mu^* = \max_i \mu_i$. A policy is a sequence of probability kernels $\pi_t$ from histories
$(a_1, x_1, \dots, a_{t-1}, x_{t-1})$ to arms, measurable in the history. The canonical bandit model is the
probability law $\mathbb{P}_{\nu,\pi}$ on $(\{1, \dots, k\} \times \mathbb{R})^n$ obtained by alternately applying
$\pi_t$ and the reward distribution $P_{A_t}$ of the chosen arm. The pull count of arm $i$ is
$T_i(n) = \#\{t \le n : A_t = i\}$ and the regret is $R_n = n\mu^* - \mathbb{E}_{\nu,\pi}[\sum_{t \le n} X_t]$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.5 (regret, pull counts) and Section 4.6 (policies as probability kernels, the density (4.7) of the canonical bandit model and Proposition 4.8). <https://tor-lattimore.com/downloads/book/book.pdf>
