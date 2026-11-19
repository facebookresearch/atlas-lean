# Continued fraction of a paperfolding sum via the words $A_k$

Let $x = (x_k)_{k \ge 0}$ be
natural numbers with $x_0 = 2$ and $x_k \ge 2$ for all $k$, let $s_k$ be the paperfolding sum
terms defined by $x$, and let $S = \sum_{k \ge 0} s_k$, with continued fraction expansion
$[a_0; a_1, a_2, \ldots]$. Let $A_k$ be the continued-fraction words defined by $x$, so that
$A_0 = (1, 1)$ and $A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$, where the mirror image $A^r$ of a
word $A$ is obtained by reversing $A$ and then replacing a leading $2$ by $1, 1$, or two leading
letters $1, 1$ by $2$, leaving any other word unchanged. Then $a_0 = 1$, and for every $k$ the
partial quotients $a_1, a_2, \ldots$ begin with the word $A_k$.

## Sources

- Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15 (`jis-2026-26.3.6-cor-15`).
