# $\tau_{-k}$ and partition convolutions modulo a prime

Let $l$ be an odd prime, let $k$ be a
natural number with $2 \le k < l$, let $n$ be a natural number, and write $p(s)$ for the number of
partitions of $s$. Then

$$\tau_{-k}(n + 1) \equiv \sum_{s=0}^{\lfloor n/l \rfloor} \tau_{l-k}(n - ls + 1)\, p(s) \pmod{l},$$

and the composition sum $\sum p(a_1) p(a_2) \cdots p(a_k)$, taken over all $k$-tuples
$(a_1, \dots, a_k)$ of natural numbers with $a_1 + \cdots + a_k = n$, is congruent modulo $l$ to
the same right-hand side.

The record prints $\tau_{l-k}(t)$ in place of $\tau_{l-k}(t + 1)$, writing $n = t + ls$; that is
false. The proof's identity
$\prod (1 - q^m)^{-k} \equiv \prod (1 - q^m)^{l-k} (1 - q^{lm})^{-1} \pmod{l}$ together with
Definition 1.1 ($\prod (1 - q^m)^j = \sum \tau_j(t + 1) q^t$) gives $\tau_{l-k}(t + 1)$;
Corollary 4.3 (the record's Corollary 6) uses this shifted form, $\omega(t) = \tau_1(t + 1)$.

## Sources

- S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 21.
