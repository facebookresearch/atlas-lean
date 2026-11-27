# Expected density of random-order minimizers

Fix integers $k \ge 1$ and $w \ge 2$ and a total order $<$ on the $k$-mers over an alphabet $\Sigma$ of size $\sigma$. For a sequence $S$ let $m_0, m_1, \dots, m_{|S|-k}$ be its $k$-mers in order and let the window $W_i = (m_i, \dots, m_{i+w-1})$. The minimizer (winnowing) scheme selects, in every window, the position of its smallest $k$-mer (ties broken by position). Writing $A(S,k)$ for the set of selected positions, the density of the scheme on $S$ is

$$d(A,S,k) = \frac{|A(S,k)|}{|S|-k+1}, \tag{1}$$

the expected density $d(A,k)$ is its expectation over sequences whose letters are independent and uniform, and the density factor is $df(A,k) = d(A,k)\,(w+1)$.

**Theorem.** Assume that in every window of $w+1$ consecutive $k$-mers each of the $w+1$ positions is equally likely, with probability $1/(w+1)$, to hold the smallest $k$-mer (this holds, up to ties, for an order drawn uniformly at random). Then

$$d(A,k) = \frac{2}{w+1}, \qquad df(A,k) = 2 .$$

A *local scheme* is any rule that picks a position in a window as a function of the window content alone. Every local scheme has expected density at least $1.5/(w+1)$, so random-order minimizers are within a factor $4/3$ of this bound.

## Expansion

Say that window $W_i$ is *charged* if it selects a position different from the one selected by $W_{i-1}$; the number of selected positions equals the number of charged windows (plus the first window), so the density is the probability that $W_i$ is charged. Look at the merged window $W_i' = (m_{i-1}, \dots, m_{i+w-1})$ of $w+1$ $k$-mers and its minimum $m$. If $m$ is at position $i-1$, the previous selection has left $W_i$ and a new one must be made; if $m$ is at position $i+w-1$, a new minimum has just entered; in every other case $W_{i-1}$ and $W_i$ share their minimum and $W_i$ is not charged. Under the uniform-position assumption the two charging events have total probability $2/(w+1)$. The density can be computed exactly, for small $k+w$, by evaluating (1) on a de Bruijn sequence of order $k+w$, because every window context then occurs exactly once. Lexicographic order violates the uniform-position assumption (for instance on runs of a repeated letter) and has density above $2/(w+1)$.

## Sources

- G. Marçais, D. Pellow, D. Bork, Y. Orenstein, R. Shamir, C. Kingsford, "Improving the performance of minimizers and winnowing schemes", *Bioinformatics* (2017), Section 1 (Eq. (1), local schemes and the $1.5/(w+1)$ lower bound), Section 2 (Hypothesis 1, Eq. (2)), Section 3.1 (Theorem 1 and proof) and Section 3.2, <https://doi.org/10.1093/bioinformatics/btx235> (PMC5870760).
