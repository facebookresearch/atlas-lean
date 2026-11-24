# Counting tuples up to rotation and left multiplication

Let $G$ be a finite group and let
$n \ge 1$. Let $C_n \times G$ act on $G^n$, the cyclic group $C_n$ rotating tuples and $h \in G$
multiplying every entry on the left, so that the orbit of $x = (x_0, \dots, x_{n-1})$ is the set
of tuples $(h x_m, h x_{m+1}, \dots, h x_{m+n-1})$, indices taken modulo $n$, for $m \in \mathbb{N}$
and $h \in G$. The number of these orbits is

$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d)\, N(n/d)\, |G|^{d-1},$$

where $\varphi$ is Euler's totient function and $N(e)$ is the number of $g \in G$ with $g^e = 1$.

The same formula counts the identity-product $n$-necklaces over $G$ (Theorem 5 of the paper), so
the two counts agree.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 19, with the action of Section 7 of the arXiv text (`jis-2026-26.4.6-thm-19`).
