# Power-of-four bound for the Erdős layer product

Let $N$ and $r$ be natural numbers. For
a natural number $x$ write $x\#$ for the primorial of $x$, the product of all primes $p \le x$.
Let $L = \lfloor \log_2 N \rfloor$, with $L = 0$ when $N = 0$, and let $P = 1$ if $L = 0$ and
$P = r\# \cdot \prod_{m=2}^{L} \lfloor N^{1/m} \rfloor\#$ if $L \ge 1$. Then
$P \le 4^{r + \lfloor \sqrt{N} \rfloor L}$.

This is a coarse bound, weaker than the full Erdős estimate, but much sharper than replacing the
first layer by $\lfloor N/3 \rfloor$ when $N$ is several multiples of $r$.
