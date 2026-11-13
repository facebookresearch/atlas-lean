# Generating function for set partitions by rises

Fix $k \ge 1$. For $n, r \ge 0$ let
$a_{n,r}$ be the number of words $\pi = \pi_1 \cdots \pi_n$ on the alphabet $\{0, \dots, k-1\}$
that use every letter, satisfy the restricted growth condition that each $\pi_i$ is at most the
number of distinct letters among $\pi_1, \dots, \pi_{i-1}$, and have exactly $r$ rises (the
source's $2$-rises), that is, positions $i < n$ with $\pi_i < \pi_{i+1}$. These words encode the
partitions of $[n]$ into $k$ blocks. Then, in the ring $\mathbb{Q}[[x, y]]$ of formal power
series,

$$\sum_{n, r \ge 0} a_{n,r}\, x^n y^r =
\frac{x^k y^{k-1} (1-y)^k}{\prod_{j=1}^{k} \bigl((1 - x + xy)^j - y\bigr)}.$$

## Sources

- Toufik Mansour and Augustine O. Munagi, “Enumeration of Partitions by Long Rises, Levels, and Descents”, Journal of Integer Sequences 12 (2009), Article 09.1.8, Theorem `thrise2`, lines 505-510, <https://cs.uwaterloo.ca/journals/JIS/VOL12/Munagi/munagi15.tex>.
