# Product formula for the action law of a bandit policy

Fix $k \ge 1$ arms, a horizon $n \ge 1$ and a reward table $x \in [0,1]^{n \times k}$. A randomized policy $\pi$ is given by a
probability vector $\pi_t(\cdot \mid h)$ on $\{1, \dots, k\}$ for each round $t$ and each history
$h = (a_1, r_1, \dots, a_{t-1}, r_{t-1})$ of past arms and observed rewards. On the table $x$ define, for
$a = (a_1, \dots, a_n) \in \{1, \dots, k\}^n$,

$$p_{\pi, x}(a) = \prod_{t=1}^{n} \pi_t\bigl(a_t \mid a_1, x_{1,a_1}, \dots, a_{t-1}, x_{t-1,a_{t-1}}\bigr).$$

Then $p_{\pi, x}$ is the [action law](oblivious-adversarial-bandit-model/action-law.md) of $\pi$ on $x$. In particular it is a
probability distribution on $\{1, \dots, k\}^n$, and for every $m \le n$ its marginal on the first $m$ arms, the same product
taken over $t \le m$, is the action law of $\pi$ on the first $m$ rounds of $x$. Because the table is fixed and both the
arm set and the horizon are finite, only finitely many histories occur, so no measurability condition on $\pi$ is needed.

## Proof

The action law of $n$ rounds draws $(a_1, \dots, a_{n-1})$ from the action law of the first $n - 1$ rounds and then $a_n$
from $\pi_n(\cdot \mid h)$ at their history $h$, which multiplies the mass of $(a_1, \dots, a_{n-1})$ by the last factor;
induction on $n$ gives $p_{\pi, x}$. Every factor is nonnegative. Summing the last factor over $a_n$ gives $1$, since
$\pi_n(\cdot \mid h)$ is a probability vector for the history $h$ determined by $a_1, \dots, a_{n-1}$ and $x$; this proves
the marginal statement for $m = n - 1$, and induction on $n - m$ gives it for every $m$, with total mass $1$ at $m = 0$.

## Depends on

- [Oblivious adversarial bandits](oblivious-adversarial-bandits.md)
- [Policy for an oblivious adversarial bandit](oblivious-adversarial-bandit-model/policy.md)
- [History of play on a reward table](oblivious-adversarial-bandit-model/history.md)
- [Action law of a policy on a reward table](oblivious-adversarial-bandit-model/action-law.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §11.1 (oblivious adversarial bandits and regret), the display at the start of §11.2 ($P_{ti} = \mathbb{P}(A_t = i \mid A_1, X_1, \dots, A_{t-1}, X_{t-1})$, the conditional law of the arm played in round $t$ given the history) and Theorem 3.3 (Ionescu–Tulcea: the law of the first $n$ coordinates is the product $K_1 \otimes \dots \otimes K_n$ of the kernels). <https://tor-lattimore.com/downloads/book/book.pdf>
