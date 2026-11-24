# Cosine formula for compositions with a part count in a residue class

Let $b(m, q; n)$ be the number of compositions of $n$ (all positive parts allowed) whose number of parts is congruent to $q$ modulo $m$. For natural numbers $m$, $q$ and $n$ with $q < m$, and with either $n \ge 2$, or $n \ge 1$ and $m$ odd, in $\mathbb{R}$,

$$b(m, q; n) = \frac{2^{n-1}}{m} + \frac{2}{m} \sum_{k=1}^{\lfloor (m-1)/2 \rfloor} \Bigl(2 \cos \frac{\pi k}{m}\Bigr)^{n-1} \cos \frac{\pi k (n + 1 - 2q)}{m}.$$

The case $n = 1$ with $m$ even is excluded: there the term $k = m/2$ left out of the sum is $(2\cos\frac{\pi}{2})^0 \cos\frac{\pi(2 - 2q)}{2} = \pm 1$, not $0$, and the formula fails; for $m = 2$, $q = 0$, $n = 1$ the right side is $1/2$ while $b(2, 0; 1) = 0$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 10.
