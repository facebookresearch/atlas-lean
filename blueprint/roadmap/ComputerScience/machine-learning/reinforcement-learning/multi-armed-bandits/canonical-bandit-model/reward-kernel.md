# Reward kernel of a round

For a stochastic bandit $\nu = (P_1, \dots, P_k)$ and a round $t + 1$, the reward kernel is the probability kernel
from the pairs $(h, a)$ of a history $h$ of $t$ rounds and an arm $a$ to $\mathbb{R}$ that maps $(h, a)$ to $P_a$,
whatever the history.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.7 (the kernel $P_t(\cdot \mid a_1, x_1, \dots, a_{t-1}, x_{t-1}, a_t) = P_{a_t}$). <https://tor-lattimore.com/downloads/book/book.pdf>
