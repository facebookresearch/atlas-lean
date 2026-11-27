# Characterization of the canonical bandit model

Fix $k \ge 1$ arms, a horizon $n \in \mathbb{N}$, a stochastic bandit $\nu = (P_1, \dots, P_k)$ and a policy
$\pi = (\pi_t)$. Let $H = (A_1, X_1, \dots, A_n, X_n)$ be a measurable map from a probability space
$(\Omega, \mathbb{P})$ to the histories of $n$ rounds, $(\{1, \dots, k\} \times \mathbb{R})^n$. Then the law of $H$
under $\mathbb{P}$ is the canonical law $\mathbb{P}_{\nu,\pi}$ if and only if, for every round $t \le n$:

- (a) the conditional distribution of the arm $A_t$ given $A_1, X_1, \dots, A_{t-1}, X_{t-1}$ is
  $\pi_t(\cdot \mid A_1, X_1, \dots, A_{t-1}, X_{t-1})$ almost surely, and
- (b) the conditional distribution of the reward $X_t$ given $A_1, X_1, \dots, A_{t-1}, X_{t-1}, A_t$ is $P_{A_t}$
  almost surely.

In particular, any two probability spaces carrying such random variables give them the same law. The conditional
distributions are regular conditional distributions, unique almost everywhere for the law of the variables
conditioned on. In the formal statement, arms and rounds are counted from $0$: the arm $i$ is stored as
$i - 1$, and the coordinate $t$ of $H$ is $(A_{t+1} - 1, X_{t+1})$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.6: conditions (a) and (b) on the interaction and Proposition 4.8, whose proof is Exercise 4.2. <https://tor-lattimore.com/downloads/book/book.pdf>
