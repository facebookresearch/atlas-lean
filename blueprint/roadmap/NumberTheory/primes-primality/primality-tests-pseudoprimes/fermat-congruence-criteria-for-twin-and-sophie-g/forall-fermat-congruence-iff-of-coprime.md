# Fermat's congruence for a product of coprime moduli

Let $n$ and $m$ be coprime natural
numbers with $0 < n < m$. Since $\gcd(m - n, nm) = 1$, the residue of $m - n$ is invertible in
$\mathbb{Z}/nm\mathbb{Z}$; write $u$ for its inverse. Then the equalities
$a^{m-1} = (a^{m-n} - 1)\,u\,n + a^{m-n}$ and
$(a^{m-n} - 1)\,u\,n + a^{m-n} = (a^{m-n} - 1)\,u\,m + 1$ in $\mathbb{Z}/nm\mathbb{Z}$ hold for
every integer $a$ coprime to $nm$ if and only if both $n$ and $m$ have the Fermat property: for
$k = n$ and for $k = m$, $a^{k-1} \equiv 1 \pmod{k}$ for every integer $a$ coprime to $k$.

This is the source's congruence
$a^{m-1} \equiv \frac{a^{m-n} - 1}{m - n}\,n + a^{m-n} \equiv \frac{a^{m-n} - 1}{m - n}\,m + 1
\pmod{nm}$, with the division by $m - n$ read as multiplication by $u$.

## Sources

- Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31, Theorem 1.1 (a) (`integers-2025-A31-thm-1-1`).
