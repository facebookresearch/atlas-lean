# Colored compositions with a congruence condition on the number of parts

Let $\mu \colon \mathbb{N} \to \mathbb{N}$ and let $m, q, n$ be natural numbers. The number $b_\mu(m, q; n)$ is

$$b_\mu(m, q; n) = \sum_{\substack{0 \le k \le n \\ k \bmod m \,=\, q \bmod m}} \; \sum_{\substack{(c_1, \dots, c_k) \in \mathbb{N}_{>0}^k \\ c_1 + \dots + c_k = n}} \; \prod_{i=1}^{k} \mu(c_i),$$

the number of compositions of $n$ (ordered tuples of positive integers with sum $n$) whose number of parts is congruent to $q$ modulo $m$, where a part $a$ carries one of $\mu(a)$ colors. The value $\mu(0)$ never enters. Residues use $k \bmod 0 = k$, so for $m = 0$ only compositions with exactly $q$ parts count. The empty composition of $0$ has $0$ parts, so $b_\mu(m, q; 0) = 1$ when $q \bmod m = 0$ and $b_\mu(m, q; 0) = 0$ otherwise.

For a set $A \subseteq \mathbb{N}$ with multiplicity function $\mathbf{1}_A$, write $b_A(m, q; n) = b_{\mathbf{1}_A}(m, q; n)$: it counts compositions of $n$ with all parts in $A$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 3.
