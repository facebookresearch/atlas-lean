# Preperiod and period of Fermat residues from the index of $2$

Write $F_n = 2^{2^n} + 1$.
Let $p$ be an odd prime, write $p - 1 = 2^r u$ with $u$ odd, and let $s \le r$ and $t \mid u$ be
natural numbers such that $g^{2^s t} = 2$ for some primitive root $g$ modulo $p$ (an element of
order $p - 1$ in $\mathbb{Z}/p\mathbb{Z}$). Let $k$ be the multiplicative order of $2$ modulo
$u/t$, with $k = 1$ when $t = u$. Then the sequence $n \mapsto F_{r-s+n} \bmod p$ is periodic
with period $k$, every positive period of it is a multiple of $k$, and for no $h < r - s$ is the
sequence $n \mapsto F_{h+n} \bmod p$ periodic with a positive period. Thus $n \mapsto F_n \bmod p$
has preperiod $r - s$ and primitive period $k$.

## Sources

- Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28 (2025), Article 25.8.7, Theorem 15 (ii) and (iii) (`jis-2025-25.8.7-thm-15`).
