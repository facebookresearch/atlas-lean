# A stationary initial law makes the chain a stationary process

Let $Q$ be a rate matrix on a finite set $S$, let $\pi$ be a probability vector on $S$ with $\pi Q = 0$, and let the chain start from a state drawn from $\pi$: its path law is $\mathbb P_\pi = \sum_i \pi_i\,\mathbb P_i$, with $\mathbb P_i$ the law of the path started at $i$. Then $\mathbb P_\pi(X_t = j) = \pi_j$ for every $t \ge 0$ and $j \in S$, and for all times $0 \le t_0 \le \dots \le t_{n-1}$, states $j_0, \dots, j_{n-1}$ and $h \ge 0$, $\mathbb P_\pi(X_{t_k + h} = j_k \text{ for all } k) = \mathbb P_\pi(X_{t_k} = j_k \text{ for all } k)$. In particular a finite birth–death chain started from its stationary law has that law at every time.

Proof. By the finite-dimensional formula, $\mathbb P_\pi(X_{t_k} = j_k \text{ for all } k) = \sum_i \pi_i e^{t_0Q}(i, j_0)\prod_{k \ge 1} e^{(t_k - t_{k-1})Q}(j_{k-1}, j_k)$. Since $\pi Q = 0$ is equivalent to $\pi e^{tQ} = \pi$ for all $t \ge 0$, the sum over $i$ equals $\pi_{j_0}$, independent of $t_0$; the remaining factors depend only on the differences $t_k - t_{k-1}$, which a shift by $h$ leaves unchanged. The case $n = 1$ gives the one-time marginals.

## Depends on

- [Path of a continuous-time Markov chain](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md): the path of the chain.
- [Law of the driving step sequence of a Markov chain](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md): the law of the driving step sequence.

## Proof depends on

- [Finite-dimensional distributions](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md): finite-dimensional distributions of the path started at a state.
- [Invariance under the semigroup](vec-mul-eq-zero-iff-forall-vec-mul-ctmc.md): $\pi Q = 0$ if and only if $\pi e^{tQ} = \pi$ for all $t \ge 0$.

## Background

- [Stationary law of a finite birth–death chain](../../birth-death-processes/stationary-law-of-a-finite-birth-death-chain.md): the stationary law of a finite birth–death chain.

## Sources

- K. Sigman, *Continuous-Time Markov Chains* (lecture notes, IEOR 6711), Columbia University, 2009, Section 1.10, Proposition 1.2, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-CTMC.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
