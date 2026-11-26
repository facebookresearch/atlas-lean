# Regret of the uniform policy with two arms

Let $k = 2$, let $n \ge 1$ and let $\pi$ choose each arm with probability $1/2$ in every round, independently of the
history. For every reward table $x \in [0,1]^{n \times 2}$,

$$R_n(\pi, x) = \tfrac12 \Bigl\lvert \sum_{t=1}^n (x_{t,1} - x_{t,2}) \Bigr\rvert.$$

For example, the table with $x_{t,1} = 1$ and $x_{t,2} = 0$ for every $t$ gives $R_n(\pi, x) = n/2$, so the uniform policy
has regret linear in $n$ on this table; for $n = 2$ the regret is $1$.

## Proof

Under the action law of $\pi$ each $A_t$ is uniform on $\{1, 2\}$, so $\mathbb{E}[\sum_t x_{t,A_t}] = \tfrac12 (S_1 + S_2)$ with
$S_i = \sum_t x_{t,i}$, and $\max(S_1, S_2) - \tfrac12 (S_1 + S_2) = \tfrac12 \lvert S_1 - S_2 \rvert$.

## Depends on

- [Oblivious adversarial bandits](oblivious-adversarial-bandits.md)
- [Policy for an oblivious adversarial bandit](oblivious-adversarial-bandit-model/policy.md)
- [Product formula for the action law of a bandit policy](action-law-of-a-bandit-policy-on-a-fixed-reward-table.md)
- [Expectation under a probability mass function](../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect.md)

## Proof depends on

- [Expectation of a finite sum](../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect-sum.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §11.1 (oblivious adversarial bandits and regret) and §11.2 (losses $y_{ti} = 1 - x_{ti}$). <https://tor-lattimore.com/downloads/book/book.pdf>
