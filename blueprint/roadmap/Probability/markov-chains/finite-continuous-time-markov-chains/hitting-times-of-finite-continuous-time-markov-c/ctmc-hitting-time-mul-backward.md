# Backward equations for the product moment of two hitting times

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a finite set $S$, with exit rates $q(i) = -Q(i, i)$ and [jump matrix](../finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md) $\Pi$. Write $\mathbb E_i$ for the expectation, under the [law of the step sequence](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md), of a functional of the chain started at $i$, and $H_A$ for the [hitting time](ctmc-hitting-time.md) of $A \subseteq S$, valued in $[0, \infty]$. Let $A, B \subseteq S$ and let $m_A, m_B, f : S \to \mathbb{R}$ be nonnegative with
$(Q m_A)(i) = -1$ for $i \notin A$, $(Q m_B)(i) = -1$ for $i \notin B$, and
$(Qf)(i) = -(m_A(i) + m_B(i))$ for $i \notin A \cup B$. Then

1. $\mathbb E_i[H_A H_B] \le f(i)$ for every $i$; in particular it is finite;
2. $\mathbb E_i[H_A H_B] = 0$ for $i \in A \cup B$;
3. the real vector $p(j) = \mathbb E_j[H_A H_B]$ satisfies
   $(Qp)(i) = -(\mathbb E_i H_A + \mathbb E_i H_B)$ for every $i \notin A \cup B$, where
   $\mathbb E_i H_A$ and $\mathbb E_i H_B$ are read as real numbers (an infinite value as $0$).
