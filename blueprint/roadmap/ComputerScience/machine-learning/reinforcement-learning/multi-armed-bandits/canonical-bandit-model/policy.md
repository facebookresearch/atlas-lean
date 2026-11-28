# Policy for a stochastic bandit

A policy for $k$ arms is a sequence $\pi = (\pi_t)_{t \ge 1}$ of probability kernels, $\pi_t$ from the histories
$(a_1, x_1, \dots, a_{t-1}, x_{t-1})$ of the first $t - 1$ rounds to the arms, measurable in the history: $\pi_t$
gives the law of the arm chosen in round $t$. The sequence runs over all rounds, so the same policy serves every
horizon. In the formal statement, arms and rounds are counted from $0$, the arm $i$ being stored as $i - 1$: the
kernel indexed by $t$ reads the histories of $t$ rounds, and it is $\pi_{t+1}$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.6, Definition 4.7, where a policy for the horizon $n$ is the sequence $(\pi_t)_{t=1}^n$. <https://tor-lattimore.com/downloads/book/book.pdf>
