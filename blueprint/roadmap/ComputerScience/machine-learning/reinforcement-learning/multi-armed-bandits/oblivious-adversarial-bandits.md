# Oblivious adversarial bandits

In a $k$-armed oblivious adversarial bandit with horizon $n$, an adversary fixes a reward table
$x \in [0,1]^{n \times k}$ before play begins. At each round $t = 1, \dots, n$ a (possibly randomized)
policy $\pi$ chooses an arm $A_t \in \{1, \dots, k\}$ based only on its past choices and the rewards
$x_{1,A_1}, \dots, x_{t-1,A_{t-1}}$ it observed, and then observes only $x_{t,A_t}$.
The regret of $\pi$ on $x$ is

$$R_n(\pi, x) = \max_{i \in [k]} \sum_{t=1}^n x_{t,i} - \mathbb{E}\Big[\sum_{t=1}^n x_{t,A_t}\Big],$$

where the expectation is over the policy's internal randomization.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §11.1. <https://tor-lattimore.com/downloads/book/book.pdf>
