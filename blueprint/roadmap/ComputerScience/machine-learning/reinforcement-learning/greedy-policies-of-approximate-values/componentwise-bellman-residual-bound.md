# Componentwise Bellman residual bound for a greedy policy

Let $S$ and $A$ be finite nonempty sets of states and actions. Consider a
Markov decision process with real one-step expected rewards $r(s,a)$ and
transition probabilities $P(s,a,s')\ge 0$ such that
$\sum_{s'\in S}P(s,a,s')=1$ for every $(s,a)$. Fix $0\le\gamma<1$. Write
$T$ for the Bellman optimality operator, $T_\sigma$ for the Bellman operator
of a deterministic stationary policy $\sigma:S\to A$, $V^\sigma$ for its
value, and $V^*$ for the optimal value. For each $\sigma$ write
$P_\sigma(s,s')=P(s,\sigma(s),s')$. For a reward vector $c:S\to\mathbb R$,
let $R_\sigma(c)$ be the value of the Markov reward process with transition
matrix $P_\sigma$, discount $\gamma$ and reward $c$. Munos writes this value
as $(I-\gamma P_\sigma)^{-1}c$; the Bellman equation for the process is
$(I-\gamma P_\sigma)R_\sigma(c)=c$.

For any $W:S\to\mathbb R$, any deterministic stationary policy $\pi$ greedy
with respect to $W$ (so $T_\pi W=TW$), and any deterministic stationary
optimal policy $\pi^*$ (so $V^{\pi^*}=V^*$), the loss is bounded by

$$
0 \le V^*-V^\pi \le R_{\pi^*}(|TW-W|)+R_\pi(|TW-W|).
$$

Both inequalities and the absolute value are componentwise. The statement
allows every choice among tied maximizers for $\pi$. An optimal $\pi^*$
exists: one can take a policy greedy with respect to $V^*$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Bellman optimality operator](../../../heuristic-search-and-planning/value-iteration/bellman.md)
- [Bellman operator of a policy](../../../heuristic-search-and-planning/value-iteration/policy-bellman.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)
- [Value of a Markov reward process](../stochastic-policies-and-discounted-occupancy/mrp-value.md)

## Proof depends on

- [A policy's Bellman update is at most the optimal one](../../../heuristic-search-and-planning/value-iteration/policy-bellman-le-bellman.md)
- [A policy's value satisfies its Bellman equation](../../../heuristic-search-and-planning/value-iteration/policy-bellman-policy-value.md)
- [A greedy policy for the optimal value is optimal](../../../heuristic-search-and-planning/value-iteration/policy-value-greedy.md)
- [No deterministic policy beats the optimal value](../../../heuristic-search-and-planning/value-iteration/policy-value-le-optimal-value.md)
- [The value of a Markov reward process solves its Bellman equation](../stochastic-policies-and-discounted-occupancy/mrp-value-eq.md)
- [The Markov reward process Bellman equation determines its value](../stochastic-policies-and-discounted-occupancy/eq-mrp-value.md)
- [Monotonicity of Markov reward process value in the reward](../stochastic-policies-and-discounted-occupancy/mrp-value-mono.md)
- [Negating the reward negates the Markov reward process value](../stochastic-policies-and-discounted-occupancy/mrp-value-neg.md)

## Proof

For each $\sigma$, $P_\sigma$ is row-stochastic because the MDP is
stochastic. The Bellman equation of the Markov reward process gives a
solution to $(I-\gamma P_\sigma)u=c$ for every $c$. The square matrix is
therefore invertible, so this interpretation of $R_\sigma$ agrees with
the inverse in (4.6).

Put $e=TW-W$, the signed Bellman residual. By the policy Bellman equation
and the affine form of $T_\sigma$,

$$
V^\sigma-W=(T_\sigma W-W)+\gamma P_\sigma(V^\sigma-W).
$$

This is the Markov reward process Bellman equation with reward
$T_\sigma W-W$, so uniqueness gives
$V^\sigma-W=R_\sigma(T_\sigma W-W)$. For $\pi$ the reward is $e$; for
$\pi^*$ it is at most $e$, so monotonicity gives $V^*-W\le R_{\pi^*}(e)$.
Subtracting gives the signed comparison. Since $e\le |e|$ and
$-e\le |e|$, monotonicity and $R_\pi(-e)=-R_\pi(e)$ give

$$
0\le V^*-V^\pi\le R_{\pi^*}(e)-R_\pi(e)
    \le R_{\pi^*}(|e|)+R_\pi(|e|).
$$

The first inequality is optimality. At $\gamma=0$, $R_\sigma(c)=c$ for
every policy, so the signed comparison gives zero loss even if $e\ne 0$.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384). [Author manuscript, HAL inria-00124685 v1](https://inria.hal.science/inria-00124685v1/document), §4.2, Lemma 4.3, equation (4.6).
