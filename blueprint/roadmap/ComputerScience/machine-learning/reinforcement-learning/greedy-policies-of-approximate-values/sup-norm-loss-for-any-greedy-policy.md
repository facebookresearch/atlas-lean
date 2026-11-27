# Sup-norm loss for any greedy policy

Let $S$ and $A$ be finite nonempty sets of states and actions. Consider a
Markov decision process with real one-step expected rewards $r(s,a)$ and
transition probabilities $P(s,a,s') \ge 0$ with $\sum_{s'\in S} P(s,a,s')=1$
for every $(s,a)$. Fix $0\le\gamma<1$. Write $T$ for the Bellman optimality
operator, $T_\pi$ for the Bellman operator of a deterministic stationary policy
$\pi:S\to A$, $V^*$ for the optimal value, and $V^\pi$ for the value of $\pi$.
Use $\|U\|_\infty=\max_{s\in S}|U(s)|$ for $U:S\to\mathbb R$.

For any $W:S\to\mathbb R$ and any $\pi$ greedy with respect to $W$, meaning
$T_\pi W=TW$, the policy loss satisfies

$$
\|V^*-V^\pi\|_\infty \le \frac{2\gamma}{1-\gamma}\|V^*-W\|_\infty.
$$

The greedy condition permits every maximizing action, including all ties.

## Proof

Write $d=\|V^*-W\|_\infty$ and $L=\|V^*-V^\pi\|_\infty$. By the two
Bellman fixed-point identities and $T_\pi W=TW$, insert $TW$ between
$TV^*$ and $T_\pi V^\pi$. The triangle inequality and the two
$\gamma$-contractions give

$$
L \le \|TV^*-TW\|_\infty + \|T_\pi W-T_\pi V^\pi\|_\infty
  \le \gamma d + \gamma(d+L).
$$

Rearrange and divide by $1-\gamma>0$. This is the argument leading to
Munos's equation (2.3), for the particular iterate $W=V_n$ there.

## Comparison

The [pointwise loss bound for the chosen greedy policy](optimal-value-sub-policy-value-greedy-le.md)
uses a fixed argmax selection. Here the policy is an input constrained only by
the greedy condition.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384). [Author manuscript, HAL inria-00124685 v1](https://www.cs.berkeley.edu/~pabbeel/cs287-fa09/readings/Munos-avi-siam.pdf), Preliminaries and §2, equation (2.3).
