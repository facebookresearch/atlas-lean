# One-step error bound for return-based control with increasingly greedy targets

For iterates $Q_{k+1} = \mathcal{R}_kQ_k$ with Markovian admissible traces, arbitrary behaviour policies, increasingly greedy targets with $T^{\pi_k}Q_k \ge TQ_k - \varepsilon_k\|Q_k\|e$, and $T^{\pi_0}Q_0 \ge Q_0$, the error obeys $\|Q_{k+1} - Q^*\| \le \gamma\|Q_k - Q^*\| + \varepsilon_k\|Q_k\|$.

Let $M$ be a Markov decision process with a finite nonempty set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. Let $T$ be the Bellman optimality operator on Q-functions, $Q^*$ the optimal action value, $\|\cdot\|$ the sup norm and $e$ the Q-function equal to $1$. For $k \ge 0$ let $\mu_k$ (behaviour) and $\pi_k$ (target) be stochastic policies, which may depend on $Q_0, \dots, Q_k$, and let $c_k : A \times X \to [0,\infty)$ be Markovian traces with $\mu_k(b \mid y)\, c_k(b,y) \le \pi_k(b \mid y)$ for all $y, b$. Let $\mathcal{R}_k$ be the return-based operator of $(\pi_k, \mu_k, c_k)$ and $Q_{k+1} = \mathcal{R}_kQ_k$. Assume:

1. $(\pi_k)$ is increasingly greedy with respect to $(Q_k)$;
2. there are reals $\varepsilon_k \ge 0$ with $T^{\pi_k}Q_k \ge TQ_k - \varepsilon_k\|Q_k\|\,e$ for every $k$;
3. $T^{\pi_0}Q_0 \ge Q_0$.

Then for every $k \ge 0$,

$$\|Q_{k+1} - Q^*\| \le \gamma\, \|Q_k - Q^*\| + \varepsilon_k\, \|Q_k\| .$$

Hypothesis 3 holds for the pessimistic start $Q_0 = -\frac{R}{1-\gamma}e$ whenever $|r| \le R$. Hypothesis 2 holds with the same $\varepsilon_k$ when $\sum_b |\pi_k(b \mid y) - \pi^g_k(b \mid y)| \le \varepsilon_k$ at every state, for a policy $\pi^g_k$ supported on maximizers of $Q_k$. The traces must be Markovian here; in Munos et al., history-dependent traces are covered only by their policy-evaluation result.

## Depends on

- [Operator form of the return-based operator for Markovian traces](../operator-form-for-markovian-traces.md)
- [Increasingly greedy sequence of policies](increasingly-greedy-policies.md)
- [Q-function Bellman optimality operator](../q-function-bellman-optimality-operator.md)
- [The optimal action value is the unique fixed point of the Q-function optimality operator](../optimal-action-value-fixed-point.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)
- [Return-based off-policy operator](../return-based-off-policy-operator.md)
- [Causal trace](../causal-trace.md)

## Proof depends on

- [Operator form of the return-based operator for Markovian traces](../operator-form-for-markovian-traces.md)
- [Error matrix of a Markovian trace](../error-matrix-of-a-markovian-trace.md)
- [Bellman residuals stay nonnegative under increasingly greedy targets](bellman-residuals-stay-nonnegative.md)
- [Q-function Bellman optimality operator](../q-function-bellman-optimality-operator.md)
- [The optimal action value is the unique fixed point of the Q-function optimality operator](../optimal-action-value-fixed-point.md)
- [Q-function Bellman operator of a stochastic policy](../q-function-bellman-operator.md)

## Expansion

Write $P_k = P^{c_k\mu_k}$, $G_k = (I - \gamma P_k)^{-1}$ and $\xi_k = T^{\pi_k}Q_k - Q_k$, so that $Q_{k+1} = Q_k + G_k\xi_k$.

*Upper bound.* Since $TQ^* = Q^* \ge T^{\pi_k}Q^*$, one gets $Q_{k+1} - Q^* = G_k[T^{\pi_k}Q_k - Q^* - \gamma P_k(Q_k - Q^*)] \le G_k[\gamma P^{\pi_k}(Q_k - Q^*) - \gamma P_k(Q_k - Q^*)] = E_k(Q_k - Q^*)$ with $E_k = \gamma G_k(P^{\pi_k} - P_k)$, using $G_k \ge 0$. As $E_k \ge 0$ has row sums at most $\gamma$, $Q_{k+1} - Q^* \le \gamma\|Q_k - Q^*\|e$.

*Lower bound.* Let $\pi^*$ put all its mass on maximizers of $Q^*$, so $T^{\pi^*}Q^* = TQ^* = Q^*$, and $TQ_k \ge T^{\pi^*}Q_k$. Then $Q_{k+1} = T^{\pi_k}Q_k + \gamma P_k G_k \xi_k$ and $\xi_k \ge 0$ give $Q_{k+1} - Q^* \ge T^{\pi_k}Q_k - T^{\pi^*}Q^* \ge T^{\pi^*}Q_k - T^{\pi^*}Q^* - \varepsilon_k\|Q_k\|e = \gamma P^{\pi^*}(Q_k - Q^*) - \varepsilon_k\|Q_k\|e \ge -(\gamma\|Q_k - Q^*\| + \varepsilon_k\|Q_k\|)e$.

The two bounds give the claim. The main-text sketch of the source carries $\gamma\varepsilon_k$ in one line of its equation (5); the constant here is the one of the full proof in Appendix C. For the pessimistic start, $T^{\pi_0}Q_0 - Q_0 = r + R \ge 0$ because $P^{\pi_0}e = e$. For the $\ell_1$ form of hypothesis 2, $|\sum_b (\pi_k - \pi^g_k)(b \mid y) Q_k(y,b)| \le \varepsilon_k\|Q_k\|$ and $\gamma \le 1$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 3.2, Theorem 2 (the per-step bound) with its hypotheses and the pessimistic initialization; full proof in Appendix C, equations (10)–(16).
