# A stationary initial law makes the chain a stationary process

Let $Q$ be a rate matrix on a finite set $S$, let $\pi$ be a probability vector on $S$ with $\pi Q = 0$, and let the chain start from a state drawn from $\pi$. Its [path law](ctmc-path-measure.md) is the probability measure $\mathbb P_\pi = \sum_i \pi_i\,\mathbb P_i$, with $\mathbb P_i$ the law of the path started at $i$. Then $\mathbb P_\pi(X_t = j) = \pi_j$ for every $t \ge 0$ and $j \in S$. For any finite sequence of nondecreasing observation times $t_0,\ldots,t_{n-1}\ge 0$, corresponding states $j_0,\ldots,j_{n-1}$, and shift $h\ge 0$, the joint probabilities satisfy $\mathbb P_\pi(X_{t_k + h} = j_k \text{ for all } k) = \mathbb P_\pi(X_{t_k} = j_k \text{ for all } k)$. In particular a finite birth–death chain started from its stationary law has that law at every time.

Proof. The [finite-dimensional formula for a fixed start](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md) gives, for $n\ge 1$, $\mathbb P_\pi(X_{t_k} = j_k \text{ for all } k) = \sum_i \pi_i e^{t_0Q}(i, j_0)\prod_{k \ge 1} e^{(t_k - t_{k-1})Q}(j_{k-1}, j_k)$. By [invariance under the semigroup](vec-mul-eq-zero-iff-forall-vec-mul-ctmc.md), the sum over $i$ equals $\pi_{j_0}$, independently of $t_0$. The remaining factors depend only on the successive time differences, which the shift leaves unchanged. The case $n=1$ gives the one-time marginal; for $n=0$ both events are the whole path space.

## Background

- [Stationary law of a finite birth–death chain](../../birth-death-processes/stationary-law-of-a-finite-birth-death-chain.md): the stationary law of a finite birth–death chain.

## Sources

- K. Sigman, *Continuous-Time Markov Chains* (lecture notes, IEOR 6711), Columbia University, 2009, Section 1.10, Proposition 1.2, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-CTMC.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
