# Regret in reward form equals regret in loss form

Fix $k \ge 1$ arms, a horizon $n \ge 1$, a reward table $x \in [0,1]^{n \times k}$ and a randomized policy $\pi$, and let
$y = 1 - x$ entrywise be the loss table. With $A$ distributed by the action law of $\pi$ on $x$,

$$R_n(\pi, x) = \mathbb{E}\Big[\sum_{t=1}^n y_{t,A_t}\Big] - \min_{i \in [k]} \sum_{t=1}^n y_{t,i}.$$

If a policy $\pi'$ that observes losses is defined by
$\pi'_t(\cdot \mid a_1, \ell_1, \dots, a_{t-1}, \ell_{t-1}) = \pi_t(\cdot \mid a_1, 1 - \ell_1, \dots, a_{t-1}, 1 - \ell_{t-1})$, then $\pi'$ on $y$
has the same action law as $\pi$ on $x$, so the loss regret of $\pi'$ on $y$, $\mathbb{E}\big[\sum_{t=1}^n y_{t,A'_t}\big] - \min_{i \in [k]} \sum_{t=1}^n y_{t,i}$ with $A'$ distributed by the action law of $\pi'$ on $y$, equals $R_n(\pi, x)$.

## Proof

For every arm sequence, $\sum_t y_{t,a_t} = n - \sum_t x_{t,a_t}$, and $\min_i \sum_t y_{t,i} = n - \max_i \sum_t x_{t,i}$; take
expectations and subtract. The observed loss is $1$ minus the observed reward, so the factors of the two action laws
agree term by term.

## Depends on

- [Oblivious adversarial bandits](oblivious-adversarial-bandits.md)
- [Policy for an oblivious adversarial bandit](oblivious-adversarial-bandit-model/policy.md)
- [Action law of a policy on a reward table](oblivious-adversarial-bandit-model/action-law.md)
- [Product formula for the action law of a bandit policy](action-law-of-a-bandit-policy-on-a-fixed-reward-table.md)
- [Expectation under a probability mass function](../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect.md)

## Proof depends on

- [Expectation of a finite sum](../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect-sum.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §11.1 (oblivious adversarial bandits and regret) and §11.2 (losses $y_{ti} = 1 - x_{ti}$). <https://tor-lattimore.com/downloads/book/book.pdf>
