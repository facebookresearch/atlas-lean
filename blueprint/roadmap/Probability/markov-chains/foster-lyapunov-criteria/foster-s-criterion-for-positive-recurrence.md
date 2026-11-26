# Foster's criterion for positive recurrence

Let $X$ be an irreducible [Markov chain](../construction-of-markov-chains/markov-chain-construction.md) on a countable state space $S$ with transition matrix $P$, and let $\tau_{x^*} = \min\{n \ge 1 : X_n = x^*\}$ be the return time to a state $x^*$. Suppose there are a function $V : S \to [0, \infty)$, a finite set $F \subset S$ and a constant $b < \infty$ with

$$
PV(x) - V(x) \le -1 + b\,\mathbf 1_F(x) \qquad \text{for all } x \in S .
$$

Then $X$ has an invariant probability distribution (it is positive recurrent), and for every $x^*$ there is $b_{x^*} < \infty$ with $E_x[\tau_{x^*}] \le V(x) + b_{x^*}$ for all $x$. Conversely, a positive recurrent irreducible chain admits such a $V$, $F$ and $b$.

For example, the length of a queue observed at departure epochs, $L_{k+1} = L_k - \mathbf 1\{L_k > 0\} + A_{k+1}$ with i.i.d. arrival counts of mean $\rho < 1$, satisfies the drift condition with $V(n) = n/(1 - \rho)$ and $F = \{0\}$.

## Depends on

- [Markov chain construction](../construction-of-markov-chains/markov-chain-construction.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- invariant probability distributions and positive recurrence of chains on a countable state space, with the equivalence between an invariant probability distribution and finite mean return times for irreducible chains;
- the comparison theorem for nonnegative functions satisfying a drift inequality (Theorem 3.2 of the first source), which gives the bound on $E_x[\tau_{x^*}]$.

## Sources

- S. Meyn, *Representations and Foster–Lyapunov criteria for stability*, lecture notes, ECE 555, University of Florida, 2008, <https://faculty.eng.ufl.edu/meyn/wp-content/uploads/sites/671/archive/spm_files/Courses/ECE555-2011/555media/Sept10-Representations.pdf>, Section 3.1, condition (V2) and Theorem 3.1 (Foster's criterion), stated there for $x^*$-irreducible chains with a small set, with the proof of the direction from the drift condition to an invariant probability measure; the converse is cited there to S. P. Meyn and R. L. Tweedie, *Markov Chains and Stochastic Stability*, Springer, 1993, Chapter 11.
- F. G. Foster, "On the stochastic matrices associated with certain queuing processes", *Annals of Mathematical Statistics* 24:355–360, 1953.
