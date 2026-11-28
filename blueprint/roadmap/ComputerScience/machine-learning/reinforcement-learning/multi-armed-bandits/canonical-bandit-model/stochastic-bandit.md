# Stochastic k-armed bandit

A stochastic $k$-armed bandit is a tuple $\nu = (P_1, \dots, P_k)$ of probability measures on $\mathbb{R}$: $P_i$ is
the reward law of arm $i$. No moment assumption is made; the means and the regret concern bandits with finite
means. In the formal statement the arms are indexed from $0$, so the arm $i$ above is the arm $i - 1$ there.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.1 (a stochastic bandit is a collection of reward distributions, one for each action). <https://tor-lattimore.com/downloads/book/book.pdf>
