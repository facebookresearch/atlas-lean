# Decomposition of rational primes in a quadratic field

Let $K$ be a quadratic field of discriminant $D$, with ring of integers $\mathcal{O}_K$, let $p$ be a prime number,
and let $\left(\frac{D}{p}\right)$ be the Kronecker symbol. Then:

- if $\left(\frac{D}{p}\right) = 0$, that is if $p \mid D$, then $p$ ramifies: $p\mathcal{O}_K = \mathfrak{p}^2$ for a prime
  ideal $\mathfrak{p}$ of norm $p$;
- if $\left(\frac{D}{p}\right) = 1$, then $p$ splits: $p\mathcal{O}_K = \mathfrak{p}\overline{\mathfrak{p}}$ for a prime ideal
  $\mathfrak{p} \neq \overline{\mathfrak{p}}$ of norm $p$, where the bar is the nontrivial automorphism of $K$;
- if $\left(\frac{D}{p}\right) = -1$, then $p$ is inert: $p\mathcal{O}_K$ is a prime ideal, of norm $p^2$.

Write $K = \mathbb{Q}(\sqrt{m})$ with $m \neq 0, 1$ squarefree. An element $r + s\sqrt{m}$ ($r, s \in \mathbb{Q}$) is
integral exactly when its characteristic polynomial $X^2 - 2rX + (r^2 - ms^2)$ has integer coefficients; as $m$ is
squarefree, this gives $r = a/2$ and $s = b/2$ with $a, b \in \mathbb{Z}$ and $a^2 \equiv m b^2 \pmod 4$, which forces $a$
and $b$ to be even if $m \equiv 2, 3 \pmod 4$ and $a \equiv b \pmod 2$ if $m \equiv 1 \pmod 4$. So $\mathcal{O}_K$ has the
$\mathbb{Z}$-basis $1, \sqrt{m}$ or $1, (1 + \sqrt{m})/2$, the determinants of the trace form on these bases are $4m$ and $m$,
and $D = 4m$ if $m \equiv 2, 3 \pmod 4$ and $D = m$ if $m \equiv 1 \pmod 4$. Keune's Theorem 3.7, obtained from
the Kummer–Dedekind theorem, gives the factorization of $p\mathcal{O}_K$, with conjugate factors in the split case: for odd $p$ it is decided by the Legendre symbol $\left(\frac{m}{p}\right)$, which equals
$\left(\frac{D}{p}\right)$; for $p = 2$, the prime $2$ ramifies when $m \equiv 2, 3 \pmod 4$, that is when $D$ is even,
splits when $m \equiv 1 \pmod 8$ and is inert when $m \equiv 5 \pmod 8$. These are the cases
$\left(\frac{D}{2}\right) = 0$, $1$ and $-1$ of the Kronecker symbol at two, which is $0$ for even $D$, $1$ for
$D \equiv \pm 1 \pmod 8$ and $-1$ for $D \equiv \pm 3 \pmod 8$. The norms follow from
$N(p\mathcal{O}_K) = p^2$.

## Depends on

- [Kronecker symbol](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-sym.md)

## Proof depends on

- [Kronecker symbol with a prime denominator](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-sym-prime.md)
- [Kronecker symbol at a prime](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-at-prime.md)
- [Kronecker symbol at two](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-at-two.md)

## Sources

- F. Keune, *Number Fields*, Radboud University Press, Nijmegen (2023, version 2023-01), open access,
  <https://doi.org/10.54195/IPVU4488>: Theorem 1.9 (integers of a quadratic number field, with the proof followed here) and Example 1.44
  ($\operatorname{disc} \mathbb{Q}(\sqrt{m})$ is $4m$ for $m \equiv 2, 3 \pmod 4$ and $m$ for $m \equiv 1 \pmod 4$); §3.1, Theorem 3.6
  (Kummer–Dedekind, p. 51) and Theorem 3.7 (pp. 52–53), the factorization of $p$ in $\mathbb{Q}(\sqrt{m})$.
