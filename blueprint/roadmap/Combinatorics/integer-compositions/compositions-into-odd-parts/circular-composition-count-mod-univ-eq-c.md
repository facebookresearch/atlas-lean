# Cosine formula for circular compositions with a part count in a residue class

Let $c(m, q; n)$ be the number of circular compositions of $n$ (nonempty sets of removed edges of the cycle $C_n$, all part sizes allowed) whose number of parts is congruent to $q$ modulo $m$. For natural numbers $m$, $q$ and $n$ with $q < m$ and $n \ge 1$, in $\mathbb{R}$,

$$c(m, q; n) = -[q = 0] + \frac{2^n}{m} + \frac{2}{m} \sum_{k=1}^{\lfloor (m-1)/2 \rfloor} \Bigl(2 \cos \frac{\pi k}{m}\Bigr)^{n} \cos \frac{\pi k (n - 2q)}{m},$$

where $[q = 0]$ is $1$ if $q = 0$ and $0$ otherwise.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 10.
