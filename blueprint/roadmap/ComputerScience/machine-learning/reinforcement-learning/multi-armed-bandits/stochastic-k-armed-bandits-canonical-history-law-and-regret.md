# Stochastic k-armed bandits: canonical history law

Fix $k$ arms and a horizon $n \in \mathbb{N}$. A stochastic $k$-armed bandit is a tuple
$\nu = (P_1, \dots, P_k)$ of probability distributions on $\mathbb{R}$, one for each arm. A policy $\pi$ is a
sequence of probability kernels $\pi_t$ from histories $(a_1, x_1, \dots, a_{t-1}, x_{t-1})$ to arms, measurable
in the history. The canonical bandit model is the
probability law $\mathbb{P}_{\nu,\pi}$ on $(\{1, \dots, k\} \times \mathbb{R})^n$ of the history
$(A_1, X_1, \dots, A_n, X_n)$ obtained by alternately applying $\pi_t$ to the history so far, which gives the
law of the arm $A_t$, and the reward distribution $P_{A_t}$ of the chosen arm, which gives the law of the reward
$X_t$. For $n = 0$ it is the point mass at the empty history. In the formal statement, arms and rounds are
counted from $0$: the arm $i$ is stored as $i - 1$, the coordinate $t$ of a history holds round $t + 1$, the pair
$(A_{t+1} - 1, X_{t+1})$, and the kernel indexed by $t$ is $\pi_{t+1}$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.6: Definition 4.7 (policies as probability kernels) and the canonical bandit model $\mathbb{P}_{\nu,\pi}$, which the book defines by the density (4.7) with respect to $(\rho \times \lambda)^n$, for the counting measure $\rho$ on the arms and a $\sigma$-finite measure $\lambda$ dominating every $P_i$ (such as $\sum_i P_i$). That measure and the one above both satisfy conditions (a) and (b) of Section 4.6, so they are equal by Proposition 4.8. Section 4.7 defines the model, for general action sets, as the product of the kernels $\pi_1, P_1, \dots, \pi_n, P_n$ by the Ionescu–Tulcea theorem, where $P_t$ maps $(a_1, x_1, \dots, a_{t-1}, x_{t-1}, a_t)$ to $P_{a_t}$: the construction stated above. <https://tor-lattimore.com/downloads/book/book.pdf>
