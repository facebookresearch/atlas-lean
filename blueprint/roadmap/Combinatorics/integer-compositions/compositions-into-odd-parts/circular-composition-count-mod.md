# Colored circular compositions with a congruence condition on the number of parts

Let $\mu \colon \mathbb{N} \to \mathbb{N}$ and let $m, q, n$ be natural numbers. With $\ell_{n,S}(s)$ the least $d \in \{1, \dots, n\}$ such that $(s + d) \bmod n \in S$,

$$c_\mu(m, q; n) = \sum_{\substack{\emptyset \ne S \subseteq \{0, \dots, n-1\} \\ |S| \bmod m \,=\, |S| \bmod m \text{ with } |S| \equiv q}} \; \prod_{s \in S} \mu(\ell_{n,S}(s)),$$

where the sum runs over the nonempty sets $S \subseteq \{0, \dots, n - 1\}$ with $|S| \bmod m = q \bmod m$ (and $k \bmod 0 = k$). A nonempty set $S$ of removed edges of the cycle $C_n$ is a circular composition of $n$ with $|S|$ parts, the part after edge $s$ having size $\ell_{n,S}(s)$; so $c_\mu(m, q; n)$ counts circular compositions of $n$ whose number of parts is congruent to $q$ modulo $m$, each part $a$ carrying one of $\mu(a)$ colors. There are none for $n = 0$: $c_\mu(m, q; 0) = 0$. For $A \subseteq \mathbb{N}$, write $c_A = c_{\mathbf{1}_A}$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 3.
