# Return-based operators contract around the action value

If a causal trace satisfies $\mu(b \mid x_s)\, c_s(b, h_s) \le \pi(b \mid x_s)$ for every action $b$ (the source's $0 \le c_s \le \pi/\mu$ where $\mu > 0$), then for arbitrary target and behaviour policies the return-based operator satisfies $\|\mathcal{R}Q - Q^\pi\| \le \gamma\|Q - Q^\pi\|$ for every Q-function, and $Q^\pi$ is its unique fixed point.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $\pi$ (target) and $\mu$ (behaviour) be arbitrary stochastic policies; $\mu$ may give probability zero to actions that $\pi$ uses and to the initial action of a pair. Let $Q^\pi$ be the action value of $\pi$ and let $c$ be a causal trace, possibly depending on the whole history, admissible for $(\pi,\mu)$:

$$\mu(b \mid x_s)\, c_s(b, h_s) \le \pi(b \mid x_s) \quad \text{for every } s \ge 1, \text{ history } h_s \text{ and action } b .$$

Then the return-based operator $\mathcal{R}$ of $(\pi, \mu, c)$ is defined, and

$$\|\mathcal{R}Q - Q^\pi\| \le \gamma\, \|Q - Q^\pi\| \quad \text{for every Q-function } Q;$$

moreover $\mathcal{R}Q^\pi = Q^\pi$ and every fixed point of $\mathcal{R}$ equals $Q^\pi$. This is contraction toward the fixed point $Q^\pi$, the form in which the source states it; the traces covered include Retrace(λ), tree-backup and importance sampling.

## Depends on

- [Return-based off-policy operator](return-based-off-policy-operator.md)
- [Causal trace](causal-trace.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

- [State-action contraction coefficient of a return-based operator](state-action-contraction-coefficient.md)
- [The action value is a fixed point of every return-based operator](action-value-fixes-return-based-operators.md)
- [Admissible trace products have mean at most one](admissible-trace-products-mean-at-most-one.md)
- [Causal trace](causal-trace.md)
- [Return-based off-policy operator](return-based-off-policy-operator.md)

## Expansion

Admissibility gives finite trace mass, so $\mathcal{R}$ is defined. The state-action coefficient bound $|\mathcal{R}Q(x,a) - Q^\pi(x,a)| \le \eta(x,a)\|Q - Q^\pi\|$ with $\eta \le \gamma$ gives the contraction, and $Q^\pi$ is a fixed point of every such operator. A fixed point $Q$ satisfies $\|Q - Q^\pi\| = \|\mathcal{R}Q - Q^\pi\| \le \gamma\|Q - Q^\pi\|$, hence $Q = Q^\pi$. The source asserts the unique fixed point before stating the trace condition; uniqueness is proved here only under admissibility. It also remarks that the result extends to sequences of behaviour policies and to measurable action spaces with densities $\min(1, d\pi/d\mu)$; neither extension is stated here.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.1, Theorem 1 and its proof.
