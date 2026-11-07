# The sign sequence $a_{p,l}$

For natural numbers $p$ and $l$, a function
$a : \mathbb{N} \to \mathbb{Z}$ is an $a_{p,l}$-sequence when all of the following hold:
$a(n) \in \{1, -1\}$ for $1 \le n \le p-1$; $a(n) = 0$ for $n = 0$ and for every $n \ge p$;
$a(1) = 1$; $a(n) = a(p-n)$ for $1 \le n \le \lfloor (p-1)/2 \rfloor$; $a(n) = -a(l+1-n)$ for
$1 \le n \le \lfloor l/2 \rfloor$; and $a(n) = a(l+1+n)$ for $1 \le n \le p-l-2$.

The values outside $1 \le n \le p-1$ are fixed to $0$ so that uniqueness of the paper's finite
sequence becomes uniqueness of the function.

## Sources

- Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Proposition 17.
