# Bellman residuals stay nonnegative under increasingly greedy targets

Iterating return-based operators with Markovian admissible traces and increasingly greedy target policies preserves a nonnegative Bellman residual: if $T^{\pi_0}Q_0 \ge Q_0$, then $T^{\pi_k}Q_k \ge Q_k$ for every $k$.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. For $k \ge 0$ let $\mu_k$ (behaviour) and $\pi_k$ (target) be stochastic policies, let $c_k : A \times X \to [0,\infty)$ be a Markovian trace with $\mu_k(b \mid y)\, c_k(b,y) \le \pi_k(b \mid y)$ for all $y, b$, and let $\mathcal{R}_k$ be the return-based operator of $(\pi_k, \mu_k, c_k)$. The policies and traces may be chosen as functions of $Q_0, \dots, Q_k$. Let $Q_{k+1} = \mathcal{R}_k Q_k$, and assume that $(\pi_k)$ is increasingly greedy with respect to $(Q_k)$. Write $\xi_k = T^{\pi_k}Q_k - Q_k$ and

$$B_k = \gamma \bigl(P^{\pi_k} - P^{c_k\mu_k}\bigr)\bigl(I - \gamma P^{c_k\mu_k}\bigr)^{-1} .$$

Then $B_k$ has nonnegative entries and $\xi_{k+1} \ge B_k \xi_k$ for every $k$. In particular, if $\xi_0 \ge 0$, then $\xi_k \ge 0$ for every $k$.

## Depends on

- [Operator form of the return-based operator for Markovian traces](../operator-form-for-markovian-traces.md)
- [Increasingly greedy sequence of policies](increasingly-greedy-policies.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)
- [Return-based off-policy operator](../return-based-off-policy-operator.md)
- [Causal trace](../causal-trace.md)

## Proof depends on

- [Operator form of the return-based operator for Markovian traces](../operator-form-for-markovian-traces.md)
- [Error matrix of a Markovian trace](../error-matrix-of-a-markovian-trace.md)
- [Increasingly greedy sequence of policies](increasingly-greedy-policies.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)
- [Causal trace](../causal-trace.md)

## Expansion

Write $P = P^{c_k\mu_k}$ and $G = (I - \gamma P)^{-1}$. By the operator form, $Q_{k+1} = Q_k + G\xi_k$. Increasing greediness gives $T^{\pi_{k+1}}Q_{k+1} \ge T^{\pi_k}Q_{k+1}$, and

$$T^{\pi_k}Q_{k+1} - Q_{k+1} = r + (\gamma P^{\pi_k} - I)(Q_k + G\xi_k) = \xi_k + (\gamma P^{\pi_k} - I) G \xi_k = \gamma (P^{\pi_k} - P) G \xi_k = B_k \xi_k,$$

using $\xi_k = (I - \gamma P) G \xi_k$. The factor $P^{\pi_k} - P$ is entrywise nonnegative (error matrix of a Markovian trace) and so is $G$ (operator form), hence $B_k \ge 0$, and $\xi_{k+1} \ge B_k \cdots B_0\, \xi_0 \ge 0$ by induction.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.2, equation (6) in the proof sketch of Theorem 2; Appendix C, equation (16) and the induction after it.
