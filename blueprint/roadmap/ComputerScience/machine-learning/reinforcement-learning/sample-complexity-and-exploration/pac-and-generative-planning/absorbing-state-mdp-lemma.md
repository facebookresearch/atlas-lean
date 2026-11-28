# Absorbing-state MDP lemma

Making one state $s$ absorbing with per-step reward $(1-\gamma)u$ pins its value at $u$. With $u = V^\star(s)$ the optimal values do not change, and moving $u$ moves all action values by at most $|u - u'|$. This leave-one-out device decouples a state's samples from the empirical optimal values.

Let $M$ be a discounted MDP with finite state and action sets, transition kernel $P_M$, rewards $r_M$ and discount $\gamma \in (0, 1)$. For a state $s$ and a scalar $u \in \mathbb R$, the $s$-absorbing MDP $M_{s,u}$ is identical to $M$ except that $P_{M_{s,u}}(s \mid s, a) = 1$ and $r_{M_{s,u}}(s, a) = (1-\gamma)u$ for every action $a$. Write $V^\pi_{s,u}$, $Q^\pi_{s,u}$, $V^\star_{s,u}$, $Q^\star_{s,u}$ for its values. Every deterministic stationary policy $\pi$ has $V^\pi_{s,u}(s) = u$.

**Lemma.**

1. Let $u^\star = V^\star_M(s)$ and, for a deterministic stationary policy $\pi$, $u^\pi = V^\pi_M(s)$. Then $V^\star_M = V^\star_{s,u^\star}$, and $V^\pi_M = V^\pi_{s,u^\pi}$ for every such $\pi$.
2. For all states $s$, all $u, u' \in \mathbb R$ and all deterministic stationary policies $\pi$,

$$\|Q^\star_{s,u} - Q^\star_{s,u'}\|_\infty \le |u - u'| \quad\text{and}\quad \|Q^\pi_{s,u} - Q^\pi_{s,u'}\|_\infty \le |u - u'|.$$

## Depends on

- [Optimal value of a discounted Markov decision process](../../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Value of a policy](../../../../heuristic-search-and-planning/value-iteration/policy-value.md)
- [Q-value of an action](../../../../heuristic-search-and-planning/value-iteration/q-value.md)

## Proof depends on

- [Uniqueness of the solution of the Bellman optimality equation](../../../../heuristic-search-and-planning/value-iteration/eq-optimal-value-of-bellman-eq.md)
- [Uniqueness of the solution of a policy's Bellman equation](../../../../heuristic-search-and-planning/value-iteration/eq-policy-value-of-policy-bellman-eq.md)
- [No deterministic policy beats the optimal value](../../../../heuristic-search-and-planning/value-iteration/policy-value-le-optimal-value.md)

## Expansion

For part 1, $V^\star_M$ satisfies the Bellman optimality equation of $M_{s,u^\star}$: at $s$ the absorbing loop with reward $(1-\gamma)u^\star$ has value $u^\star = V^\star_M(s)$, and at every other state the transitions and rewards of $M_{s,u^\star}$ are those of $M$. Uniqueness of the fixed point gives $V^\star_M = V^\star_{s,u^\star}$; the policy case is the same with the policy's Bellman equation. For part 2, the rewards of $M_{s,u}$ and $M_{s,u'}$ differ only at $s$, by $(1-\gamma)|u - u'|$, while the transitions coincide; with $\pi_{s,u}$ optimal in $M_{s,u}$,

$$Q^\star_{s,u} - Q^\star_{s,u'} \le (I - \gamma P^{\pi_{s,u}}_{s,u'})^{-1}(r_{s,u} - r_{s,u'}) \le \frac{1}{1-\gamma}\|r_{s,u} - r_{s,u'}\|_\infty = |u - u'|,$$

where the first inequality uses that no deterministic stationary policy beats the optimal value of $M_{s,u'}$, and symmetrically. In the minimax analysis the lemma is applied to the empirical version $\hat M_{s,u}$, which uses the empirical kernel $\hat P$ at every state other than $s$; for fixed $u$ it does not depend on the generative-model samples drawn at $s$. So $\hat P(\cdot \mid s, a)$ is independent of $\hat V^\star_{s,u}$ for each fixed $u$, so Bernstein's inequality applies to $(P - \hat P)(\cdot \mid s, a)\cdot\hat V^\star_{s,u}$ for every $u$ in a finite grid, and part 2 transfers the bound to $\hat V^\star = \hat V^\star_{s,\hat V^\star(s)}$. Later work uses state-action-absorbing variants of the same construction.

## Sources

- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Section 4.2 (definition of $M_{s,u}$ and $\hat M_{s,u}$), Lemma 7 (independence and Bernstein bound), Lemma 8 and Lemma 9 with their proofs; Lemmas 8 and 9 are stated there for all stationary policies, stochastic ones included, of which the deterministic case here is a special case.
