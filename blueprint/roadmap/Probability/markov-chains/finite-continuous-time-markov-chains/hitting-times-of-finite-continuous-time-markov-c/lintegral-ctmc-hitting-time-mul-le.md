# Minimality of the product moment

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a finite set $S$, with exit rates $q(i) = -Q(i, i)$ and [jump matrix](../finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md) $\Pi$. Write $\mathbb E_i$ for the expectation, under the [law of the step sequence](../finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md), of a functional of the chain started at $i$, and $H_A$ for the [hitting time](ctmc-hitting-time.md) of $A \subseteq S$, valued in $[0, \infty]$. Let $A, B \subseteq S$ with $q(i) \ne 0$ for $i \notin A$ and for $i \notin B$, and let
$m_A, m_B, F : S \to [0, \infty]$ satisfy

$$\frac{1}{q(i)} + \sum_j \Pi(i, j)\, m_A(j) \le m_A(i) \ (i \notin A), \qquad \frac{1}{q(i)} + \sum_j \Pi(i, j)\, m_B(j) \le m_B(i) \ (i \notin B),$$

$$\frac{m_A(i) + m_B(i)}{q(i)} + \sum_j \Pi(i, j)\, F(j) \le F(i) \qquad (i \notin A \cup B) .$$

Then $\mathbb E_i[H_A H_B] \le F(i)$ for every $i \in S$.
