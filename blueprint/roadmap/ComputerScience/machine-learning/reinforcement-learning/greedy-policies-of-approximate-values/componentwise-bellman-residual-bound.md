# Componentwise Bellman residual bound for a greedy policy

Let $S$ and $A$ be finite nonempty sets of states and actions. Consider a
Markov decision process with real one-step expected rewards $r(s,a)$ and
transition probabilities $P(s,a,s')\ge 0$ such that
$\sum_{s'\in S}P(s,a,s')=1$ for every $(s,a)$. Fix $0\le\gamma<1$. Write
$T$ for the Bellman optimality operator, $T_\sigma$ for the Bellman operator
of a deterministic stationary policy $\sigma:S\to A$, $V^\sigma$ for its
value, and $V^*$ for the optimal value. For each $\sigma$ write
$P_\sigma(s,s')=P(s,\sigma(s),s')$ and $R_\sigma=(I-\gamma P_\sigma)^{-1}$,
acting on column vectors indexed by $S$.

For any $W:S\to\mathbb R$, any deterministic stationary policy $\pi$ greedy
with respect to $W$ (so $T_\pi W=TW$), and any deterministic stationary
optimal policy $\pi^*$ (so $V^{\pi^*}=V^*$), the loss is bounded by

$$
0 \le V^*-V^\pi \le (R_{\pi^*}+R_\pi)\,|TW-W|.
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

## Proof depends on

- [A policy's Bellman update is at most the optimal one](../../../heuristic-search-and-planning/value-iteration/policy-bellman-le-bellman.md)
- [A policy's value satisfies its Bellman equation](../../../heuristic-search-and-planning/value-iteration/policy-bellman-policy-value.md)
- [A greedy policy for the optimal value is optimal](../../../heuristic-search-and-planning/value-iteration/policy-value-greedy.md)
- [No deterministic policy beats the optimal value](../../../heuristic-search-and-planning/value-iteration/policy-value-le-optimal-value.md)
- [Value of a Markov reward process](../stochastic-policies-and-discounted-occupancy/mrp-value.md)
- [The value of a Markov reward process solves its Bellman equation](../stochastic-policies-and-discounted-occupancy/mrp-value-eq.md)
- [A nonnegative reward has a nonnegative value](../stochastic-policies-and-discounted-occupancy/mrp-value-nonneg.md)

## Proof

For each $\sigma$, the matrix $P_\sigma$ is row-stochastic. For every reward
vector $c$, the corresponding Markov reward process value $V_c$ satisfies
$(I-\gamma P_\sigma)V_c=c$. Thus $I-\gamma P_\sigma$ is surjective on
$\mathbb R^S$ and, being square, invertible, with $R_\sigma c=V_c$. For
an indicator reward $c=\mathbf 1_{\{s'\}}\ge 0$, the value is nonnegative.
These values are the columns of $R_\sigma$, so its entries are nonnegative
(not necessarily strictly positive). In particular it preserves
componentwise inequalities.

Put $e=TW-W$, the signed Bellman residual. By the policy Bellman equation
and the affine form of $T_\sigma$,

$$
(I-\gamma P_\sigma)(V^\sigma-W)=T_\sigma W-W.
$$

For $\pi$ the right-hand side equals $e$, giving $V^\pi-W=R_\pi e$.
For $\pi^*$ it is at most $e$, giving $V^*-W\le R_{\pi^*}e$ by order
preservation. Subtracting gives the signed comparison and then the bound:

$$
0\le V^*-V^\pi\le (R_{\pi^*}-R_\pi)e
    \le (R_{\pi^*}+R_\pi)|e|.
$$

The first inequality is optimality; the last uses $e\le |e|$ and
$-e\le |e|$ separately. At $\gamma=0$ both resolvents are $I$, so the
signed comparison already gives zero loss, even if $e\ne 0$.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384). [Author manuscript, HAL inria-00124685 v1](https://inria.hal.science/inria-00124685v1/document), §4.2, Lemma 4.3, equation (4.6).
