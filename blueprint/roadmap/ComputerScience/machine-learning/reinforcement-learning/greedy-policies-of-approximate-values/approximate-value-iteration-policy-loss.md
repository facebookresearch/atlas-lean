# Approximate value iteration policy loss

Consider an infinite-horizon discounted Markov decision process with a finite
nonempty state set $S$, a finite nonempty action set $A$, real transition rewards
$r(s,a,s')$, and transition probabilities $P(s,a,s')\ge 0$ satisfying
$\sum_{s'\in S}P(s,a,s')=1$ for every $(s,a)$. Let $0\le\gamma<1$. In the
Bellman operators $T$ (optimality) and $T_\pi$ (for a deterministic stationary
policy $\pi:S\to A$), the one-step expected reward is
$\bar r(s,a)=\sum_{s'\in S} P(s,a,s')r(s,a,s')$. Write $V^*$ for the optimal
value and $V^\pi$ for the value of $\pi$, and let
$\|U\|_\infty=\max_{s\in S}|U(s)|$ for $U:S\to\mathbb R$.

Fix an approximation operator $\mathcal A:\mathbb R^S\to\mathbb R^S$ and
an arbitrary $V_0\in\mathbb R^S$. The approximate value iterates satisfy
$V_{n+1}=\mathcal A(TV_n)$ for every $n\ge 0$. Define the step error
$\varepsilon_n=TV_n-V_{n+1}$ and suppose that for some $\varepsilon\ge 0$,
$\|\varepsilon_n\|_\infty\le\varepsilon$ for every $n\ge 0$.
For each $n$, let $\pi_n:S\to A$ be any deterministic stationary policy
that is greedy with respect to $V_n$, i.e. $T_{\pi_n}V_n=TV_n$. This means
it chooses a maximizing action in each state, with no fixed tie-breaking rule.
Then

$$
\limsup_{n\to\infty}\|V^*-V^{\pi_n}\|_\infty
    \le \frac{2\gamma}{(1-\gamma)^2}\,\varepsilon.
$$

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Bellman optimality operator](../../../heuristic-search-and-planning/value-iteration/bellman.md)
- [Bellman operator of a policy](../../../heuristic-search-and-planning/value-iteration/policy-bellman.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)

## Proof depends on

- [Bellman's operator is a contraction](../../../heuristic-search-and-planning/value-iteration/bellman-contracting.md)
- [The optimal value solves the Bellman optimality equation](../../../heuristic-search-and-planning/value-iteration/bellman-optimal-value.md)
- [Sup-norm loss for any greedy policy](sup-norm-loss-for-any-greedy-policy.md)

## Proof

Set $d_n=\|V^*-V_n\|_\infty$. Since $TV^*=V^*$, the triangle inequality,
the $\gamma$-contraction of $T$, and the step error bound give
$d_{n+1}\le\gamma d_n+\varepsilon$. Set $b=\varepsilon/(1-\gamma)$ so that
$\gamma b+\varepsilon=b$. Induction gives $d_n\le \gamma^n d_0+b$.
Applying the greedy-policy loss estimate (2.3) with $W=V_n$ and $\pi=\pi_n$
then bounds the nonnegative policy loss by
$\frac{2\gamma}{1-\gamma}(\gamma^n d_0+b)$. This upper bound tends to
$\frac{2\gamma}{1-\gamma}b$, giving (2.2) without assuming the iterates converge.

The proof uses the approximation operator only through the step error bound.
It thus also gives the same conclusion for any sequence with that bound,
even if the sequence does not come from a fixed $\mathcal A$.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384). [Author manuscript, HAL inria-00124685 v1](https://www.cs.berkeley.edu/~pabbeel/cs287-fa09/readings/Munos-avi-siam.pdf), §1, equation (1.1); Preliminaries; §2, equations (2.1)–(2.3).
