# Pairwise independent samples hit dense sets

Let $h : \iota \times X \to Y$ be pairwise independent with uniform seed, $S \subseteq X$ a set of $m$ points and $B \subseteq Y$ of density $p = |B|/|Y|$. Then

$$
\Pr_i[\exists x \in S : h_i(x) \in B] \ge \frac{\min(mp, 1)}{2}, \quad\text{and}\quad \Pr_i[\exists x \in S : h_i(x) \in B] \ge \frac{3mp}{4} \text{ when } 2mp \le 1 .
$$

Also each point is retained in $B$ with probability exactly $p$ and two distinct points with probability $p^2$, so the number of retained points has mean $mp$ and variance $mp(1-p)$ (sampling at rate $p$ with pairwise independence).

## Proof sketch

Restrict to a subset $S'$ of size $\min(m, \lceil 1/p\rceil)$. Inclusion–exclusion (Bonferroni) gives $\Pr[\exists] \ge |S'|p - \binom{|S'|}{2}p^2$ by pairwise independence, which is at least $|S'|p(1 - |S'|p/2)$, yielding both bounds.

## Depends on

- [k-wise independent hash families](../../data-structures/hashing/limited-independence-hash-families/k-wise-independent-hash-family.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
- B. Chor and O. Goldreich, "On the Power of Two-Point Based Sampling", Journal of Complexity, 1989.
- S. Goldwasser and M. Sipser, "Private Coins versus Public Coins in Interactive Proof Systems", Proceedings of the 18th ACM Symposium on Theory of Computing, 1986.
