# Convolution identity for sequences in $H(p)$

Let $p \ge 2$ be a natural number and let
$\mathcal{H} : \mathbb{Z} \to \mathbb{Z}$ be a sequence in $H(p)$, that is,
$\mathcal{H}(t) = \mathcal{H}(t-1) + \mathcal{H}(t-p) - \mathcal{H}(t-2p-1)$ for every integer
$t$. Then for all natural numbers $m \ge 1$ and $n \ge 1$,

$$
\mathcal{H}(m+n) = \mathcal{H}(m)A_p(n+1) + \sum_{i=1}^{p-1} \mathcal{H}(m-i)B_p(n-p+i+1) -
\sum_{i=0}^{p} \mathcal{H}(m-p-i)A_p(n-p+i),
$$

where $A_p, B_p : \mathbb{Z} \to \mathbb{Z}$ are the sequences in $H(p)$ with $A_p(t) = 1$ for
$1 \le t \le p$ and $A_p(t) = 0$ for $-p \le t \le 0$, and with $B_p(t) = 1$ for $1 \le t \le p$
and for $t = -p+1$ and $B_p(t) = 0$ for the other $-p \le t \le 0$.

## Sources

- "On Generalized Leonardo `p`-Numbers", Journal of Integer Sequences 27 (2024), Article 24.4.6, Corollary 11.
