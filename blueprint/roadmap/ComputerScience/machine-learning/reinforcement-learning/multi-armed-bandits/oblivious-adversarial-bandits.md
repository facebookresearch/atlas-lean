# Oblivious adversarial bandits

Fix $k \ge 1$ arms and a horizon $n \in \mathbb{N}$. In a $k$-armed oblivious adversarial bandit, an adversary fixes a
reward table $x = (x_{t,i}) \in \mathbb{R}^{n \times k}$ before play begins: $x_{t,i}$ is the reward of arm $i$ in round
$t$. A policy $\pi$ gives, for each round $t$ and each history $h = (a_1, r_1, \dots, a_{t-1}, r_{t-1})$ of the arms
chosen and the rewards observed in the earlier rounds, a probability mass function $\pi_t(\cdot \mid h)$ on the arms
$\{1, \dots, k\}$, with no measurability condition. Playing on $x$, the policy draws the arm $A_t$ from
$\pi_t(\cdot \mid A_1, x_{1,A_1}, \dots, A_{t-1}, x_{t-1,A_{t-1}})$ and observes only the reward $x_{t,A_t}$; the law of
$(A_1, \dots, A_n)$ is the action law of $\pi$ on $x$, a probability mass function on $\{1, \dots, k\}^n$. The regret of
$\pi$ on $x$ is

$$R_n(\pi, x) = \max_{i \in [k]} \sum_{t=1}^n x_{t,i} - \mathbb{E}\Big[\sum_{t=1}^n x_{t,A_t}\Big],$$

where the expectation is under the action law of $\pi$ on $x$. The source takes $k > 1$ arms and rewards in $[0, 1]$,
$x \in [0,1]^{n \times k}$; the definition applies to every $k \ge 1$ and every real table, and results that need this
range assume it. The regret can be negative: an adaptive policy can collect more reward than every fixed arm on a given
table. In the formal statement, arms and rounds are counted from $0$: the arm $i$ is stored as $i - 1$, the reward
$x_{t,i}$ is the entry $(t - 1, i - 1)$ of the table, and $\pi_t$ is the policy's distribution indexed by $t - 1$, which
reads the histories of $t - 1$ rounds.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 11.1 (adversarial bandits, policies and the regret (11.1)) and Section 11.5, Note 4 (oblivious adversaries choose the rewards before the game starts). <https://tor-lattimore.com/downloads/book/book.pdf>
