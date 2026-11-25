# Action law of a bandit policy on a fixed reward table

Fix $k \ge 1$ arms, a horizon $n \ge 1$ and a reward table $x \in [0,1]^{n \times k}$. A randomized policy $\pi$ is given by a
probability vector $\pi_t(\cdot \mid h)$ on $\{1, \dots, k\}$ for each round $t$ and each history
$h = (a_1, r_1, \dots, a_{t-1}, r_{t-1})$ of past arms and observed rewards. On the table $x$ define, for
$a = (a_1, \dots, a_n) \in \{1, \dots, k\}^n$,

$$p_{\pi, x}(a) = \prod_{t=1}^{n} \pi_t\bigl(a_t \mid a_1, x_{1,a_1}, \dots, a_{t-1}, x_{t-1,a_{t-1}}\bigr).$$

Then $p_{\pi, x}$ is a probability distribution on $\{1, \dots, k\}^n$, and for every $m \le n$ its marginal on the first $m$
arms is the same product taken over $t \le m$. The expectation in the regret of $\pi$ on $x$ is the expectation under
$p_{\pi, x}$. Because the table is fixed and both the arm set and the horizon are finite, only finitely many histories
occur, so no measurability condition on $\pi$ is needed.

## Proof

Every factor is nonnegative. Summing the last factor over $a_n$ gives $1$, since $\pi_n(\cdot \mid h)$ is a probability
vector for the history $h$ determined by $a_1, \dots, a_{n-1}$ and $x$; this proves the marginal statement for $m = n - 1$,
and induction on $n - m$ gives it for every $m$, with total mass $1$ at $m = 0$.

## Depends on

- [Oblivious adversarial bandits](oblivious-adversarial-bandits.md)
- [Expectation under a probability mass function](../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §11.1 (oblivious adversarial bandits and regret) and §11.2 (losses $y_{ti} = 1 - x_{ti}$). <https://tor-lattimore.com/downloads/book/book.pdf>
