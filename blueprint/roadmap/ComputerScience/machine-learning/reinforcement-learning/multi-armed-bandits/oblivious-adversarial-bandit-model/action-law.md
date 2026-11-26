# Action law of a policy on a reward table

Fix $k$ arms, a horizon $n \in \mathbb{N}$, a real reward table $x = (x_{t,i}) \in \mathbb{R}^{n \times k}$ and a policy
$\pi$. The action law of $\pi$ on $x$ is the probability mass function on $\{1, \dots, k\}^n$ of the arms
$(A_1, \dots, A_n)$ that $\pi$ chooses when it plays on $x$: $A_1$ has law $\pi_1(\cdot \mid \emptyset)$, and given
$A_1, \dots, A_t$, the arm $A_{t+1}$ has law $\pi_{t+1}(\cdot \mid A_1, x_{1,A_1}, \dots, A_t, x_{t,A_t})$. It is defined by
recursion on $n$: the action law for $n + 1$ rounds draws $(A_1, \dots, A_n)$ from the action law of $\pi$ on the first
$n$ rounds of $x$, then $A_{n+1}$ from $\pi_{n+1}$ at the history $(A_1, x_{1,A_1}, \dots, A_n, x_{n,A_n})$, and appends
it. For $n = 0$ it is the point mass at the empty sequence. In the formal statement, arms and rounds are counted from
$0$: the coordinate $t$ of the arm sequence is $A_{t+1} - 1$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 11.1 (in round $t$ the learner samples $A_t$ from a distribution chosen by the policy from the history; the expectation in the regret is over this randomness). <https://tor-lattimore.com/downloads/book/book.pdf>
