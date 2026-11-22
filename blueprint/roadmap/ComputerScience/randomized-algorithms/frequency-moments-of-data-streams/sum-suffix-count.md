# Suffix counts enumerate each multiplicity once

Let $\iota$ be a finite set, $l = (a_0, \dots, a_{m-1})$ a stream over $\iota$, $m_i$ the number of occurrences of $i$ in $l$ and $r_p$ the suffix count of position $p$ (the number of $q \ge p$ with $a_q = a_p$). Then for every function $g \colon \mathbb{N} \to \mathbb{R}$,

$$\sum_{p < m} g(r_p) = \sum_{i \in \iota} \sum_{r=1}^{m_i} g(r):$$

the suffix counts of the positions holding symbol $i$ are exactly $1, \dots, m_i$. This is the regrouping behind the computation of $\mathbb{E}[X]$ and $\mathbb{E}[X^2]$ in N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.1.
