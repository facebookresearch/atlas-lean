# The index of a residue and its multiplicative order

Let $p$ be a prime, let $g$ be a
primitive root modulo $p$ (an element of $\mathbb{Z}/p\mathbb{Z}$ of multiplicative order
$p - 1$), and let $a \in \mathbb{Z}/p\mathbb{Z}$. If $g^i = a$ for a natural number $i$, then
$\gcd(p - 1, i) = (p - 1)/\operatorname{ord}_p(a)$, where $\operatorname{ord}_p(a)$ is the
multiplicative order of $a$ modulo $p$.

This holds for every natural number $i$ with $g^i = a$; the paper's index
$\operatorname{ind}_g(a)$, which lies between $1$ and $p - 1$, is one of them.

## Sources

- Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28 (2025), Article 25.8.7, Lemma 8 (iv) (`jis-2025-25.8.7-lem-8`).
