# Return-based control converges to the optimal action value

Under the hypotheses of the one-step error bound for return-based control, if $\varepsilon_k \to 0$ then the iterates stay bounded and $Q_k \to Q^*$ in sup norm, for arbitrary behaviour policies.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$, real rewards and transition probabilities that are nonnegative and sum to $1$, and let $0 \le \gamma < 1$. Let $(\mu_k)$, $(\pi_k)$, Markovian traces $(c_k)$ with $\mu_k c_k \le \pi_k$, and iterates $Q_{k+1} = \mathcal{R}_kQ_k$ satisfy the hypotheses of the one-step error bound: $(\pi_k)$ increasingly greedy with respect to $(Q_k)$, $T^{\pi_k}Q_k \ge TQ_k - \varepsilon_k\|Q_k\|e$ with $\varepsilon_k \ge 0$, and $T^{\pi_0}Q_0 \ge Q_0$. If moreover $\varepsilon_k \to 0$, then $\sup_k \|Q_k\| < \infty$, more precisely $\limsup_k \|Q_k\| \le \frac{2(1+\gamma)}{1-\gamma}\|Q^*\|$, and

$$\lim_{k \to \infty} \|Q_k - Q^*\| = 0 .$$

The behaviour policies need not become greedy, so no greedy-in-the-limit exploration condition is used.

## Depends on

- [One-step error bound for return-based control with increasingly greedy targets](control-error-recursion.md)
- [The optimal action value is the unique fixed point of the Q-function optimality operator](../optimal-action-value-fixed-point.md)
- [Return-based off-policy operator](../return-based-off-policy-operator.md)
- [Causal trace](../causal-trace.md)
- [Operator form of the return-based operator for Markovian traces](../operator-form-for-markovian-traces.md)
- [Increasingly greedy sequence of policies](increasingly-greedy-policies.md)
- [Q-function Bellman optimality operator](../q-function-bellman-optimality-operator.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Proof depends on

- [One-step error bound for return-based control with increasingly greedy targets](control-error-recursion.md)
- [The optimal action value is the unique fixed point of the Q-function optimality operator](../optimal-action-value-fixed-point.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Expansion

Once $\varepsilon_k < (1-\gamma)/2$, the one-step bound and $\|Q_k - Q^*\| \le \|Q_k\| + \|Q^*\|$ give $\|Q_{k+1}\| \le (1+\gamma)\|Q^*\| + \frac{1+\gamma}{2}\|Q_k\|$, a recursion with contraction factor $(1+\gamma)/2 < 1$; hence the iterates are bounded with the stated limsup. With $\|Q_k\| \le K$, the errors $a_k = \|Q_k - Q^*\|$ satisfy $a_{k+1} \le \gamma a_k + K\varepsilon_k$ with $\varepsilon_k \to 0$, so $\limsup a_k \le \gamma \limsup a_k$ and $a_k \to 0$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.2, Theorem 2 (the consequence for $\varepsilon_k \to 0$); Appendix C, last paragraph; Section 4.2, "No GLIE assumption".
