# Order polynomial

For a finite poset $P$ and $m \in \mathbb{N}$, $\Omega_P(m)$ is the number of order-preserving maps
$\sigma \colon P \to [m]$, that is, maps with $s \le t \Rightarrow \sigma(s) \le \sigma(t)$, where
$[m]$ is the chain $\{1, \dots, m\}$ (any chain with $m$ elements gives the same count). Replacing
$\sigma(t)$ by $m + 1 - \sigma(t)$ shows that it also counts the order-reversing maps $P \to [m]$,
the $P$-partitions of a naturally labelled $P$ with parts in $[m]$.

The name is justified by the fact that $\Omega_P(m)$ is a polynomial in $m$.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Section 3.12, after Proposition 3.12.1, and Section 3.15.3.
