# Decomposition of rational primes in a quadratic field

Let $K$ be a quadratic field of discriminant $D$, with ring of integers $\mathcal{O}_K$, let $p$ be a prime number,
and let $\left(\frac{D}{p}\right)$ be the Kronecker symbol. Then:

- if $\left(\frac{D}{p}\right) = 0$, that is if $p \mid D$, then $p$ ramifies: $p\mathcal{O}_K = \mathfrak{p}^2$ for a prime
  ideal $\mathfrak{p}$ of norm $p$;
- if $\left(\frac{D}{p}\right) = 1$, then $p$ splits: $p\mathcal{O}_K = \mathfrak{p}\overline{\mathfrak{p}}$ for a prime ideal
  $\mathfrak{p} \neq \overline{\mathfrak{p}}$ of norm $p$, where the bar is the nontrivial automorphism of $K$;
- if $\left(\frac{D}{p}\right) = -1$, then $p$ is inert: $p\mathcal{O}_K$ is a prime ideal, of norm $p^2$.

Write $K = \mathbb{Q}(\sqrt{m})$ with $m \neq 0, 1$ squarefree. By the
[integrality criterion](../../../FieldTheory/extensions-and-closure/minimal-polynomials-and-integrality/is-integral-iff-coeff-mem-range.md),
an element $r + s\sqrt{m}$ ($r, s \in \mathbb{Q}$, $s \neq 0$) is integral exactly when its minimal polynomial
$X^2 - 2rX + (r^2 - ms^2)$ has integer coefficients; as $m$ is squarefree, this gives $r = a/2$ and $s = b/2$ with
$a, b \in \mathbb{Z}$ and $a^2 \equiv m b^2 \pmod 4$, which forces $a$ and $b$ to be even if $m \equiv 2, 3 \pmod 4$ and
$a \equiv b \pmod 2$ if $m \equiv 1 \pmod 4$. So $\mathcal{O}_K = \mathbb{Z}[\omega]$, where $\omega = \sqrt{m}$, with minimal
polynomial $f = X^2 - m$, if $m \equiv 2, 3 \pmod 4$, and $\omega = (1 + \sqrt{m})/2$, with
$f = X^2 - X - (m - 1)/4$, if $m \equiv 1 \pmod 4$. The determinants of the trace form on the bases $(1, \omega)$ are $4m$
and $m$, so $D = 4m$ if $m \equiv 2, 3 \pmod 4$ and $D = m$ if $m \equiv 1 \pmod 4$; in both cases $D$ is the discriminant
of $f$ and $D = (\omega - \overline{\omega})^2$.

As $\mathcal{O}_K = \mathbb{Z}[\omega]$, the [conductor](../../../RingTheory/dedekind-domains/conductor-ideal/conductor-ideal-top.md) of $\mathbb{Z}[\omega]$ in $\mathcal{O}_K$ is
$\mathcal{O}_K$, so the
[Kummer–Dedekind theorem](../discriminants-ramification/kummer-dedekind-theorem.md) applies to every prime $p$: the prime
ideal factors of $p\mathcal{O}_K$, with their multiplicities, correspond to the monic irreducible factors of $f \bmod p$, with
theirs. By the [norm of a principal ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm-principal.md),
$N(p\mathcal{O}_K) = |N_{K/\mathbb{Q}}(p)| = p^2$, and $N(\mathfrak{p}) > 1$ for every prime ideal factor $\mathfrak{p}$ of
$p\mathcal{O}_K$, whose residue ring is a nonzero quotient of the finite ring $\mathcal{O}_K / p\mathcal{O}_K$, so the
[multiplicativity of $N$](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md) gives three cases. If $f \bmod p$ is
irreducible, $p\mathcal{O}_K$ is a prime ideal, of norm $p^2$. If $f \equiv (X - c)^2 \pmod p$, then
$p\mathcal{O}_K = \mathfrak{p}^2$ with $N(\mathfrak{p}) = p$. If $f \equiv (X - c)(X - c') \pmod p$ with $c \not\equiv c'$, then
$p\mathcal{O}_K = \mathfrak{p}\mathfrak{p}'$ for prime ideals $\mathfrak{p} \neq \mathfrak{p}'$ of norm $p$, and $p \nmid D$, since
$D$ is the discriminant of $f$; then $\mathfrak{p}' = \overline{\mathfrak{p}}$, because conjugation permutes the two factors, by
[unique factorisation](../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), and
$\overline{\mathfrak{p}} = \mathfrak{p}$ would make it induce an automorphism of $\mathcal{O}_K / \mathfrak{p} \cong \mathbb{F}_p$, hence the
identity, so that $\omega - \overline{\omega} \in \mathfrak{p}$ and $D = (\omega - \overline{\omega})^2 \in \mathfrak{p} \cap \mathbb{Z} = p\mathbb{Z}$.

It remains to factor $f$ modulo $p$. For odd $p$, as $D$ is the discriminant of $f$, $f \bmod p$ has a double root if
$p \mid D$, two distinct roots if $D$ is a nonzero square modulo $p$, and none otherwise: these are the cases
$\left(\frac{D}{p}\right) = 0$, $1$ and $-1$ of the Legendre symbol, which is the Kronecker symbol at an odd prime. For
$p = 2$: if $m \equiv 2, 3 \pmod 4$, then $f \equiv (X - m)^2 \pmod 2$, so $2$ ramifies, and $D = 4m$ is even; if
$m \equiv 1 \pmod 4$, then $f \equiv X^2 + X + (m - 1)/4 \pmod 2$, which is $X (X + 1)$ when $m \equiv 1 \pmod 8$ and the
irreducible $X^2 + X + 1$ when $m \equiv 5 \pmod 8$. These are the cases $\left(\frac{D}{2}\right) = 0$, $1$ and $-1$ of the
Kronecker symbol at two, which is $0$ for even $D$, $1$ for $D \equiv \pm 1 \pmod 8$ and $-1$ for $D \equiv \pm 3 \pmod 8$.

## Depends on

- [Kronecker symbol](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-sym.md)
- [Absolute norm of an ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for the norms of the prime ideals

## Proof depends on

- [Integrality via the coefficients of the minimal polynomial](../../../FieldTheory/extensions-and-closure/minimal-polynomials-and-integrality/is-integral-iff-coeff-mem-range.md), for the ring of integers $\mathbb{Z}[\omega]$
- [Conductor ideal of the whole algebra](../../../RingTheory/dedekind-domains/conductor-ideal/conductor-ideal-top.md), for the conductor of $\mathbb{Z}[\omega] = \mathcal{O}_K$, which makes the Kummer–Dedekind theorem apply to every $p$
- [Kummer–Dedekind theorem](../discriminants-ramification/kummer-dedekind-theorem.md), for the factorisation of $p\mathcal{O}_K$ from that of $f \bmod p$
- [The absolute norm of a principal ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm-principal.md), for $N(p\mathcal{O}_K) = p^2$
- [Absolute norm of an ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for $N(IJ) = N(I) N(J)$, which gives the norms of the prime factors of $p\mathcal{O}_K$
- [Unique factorisation of ideals in a Dedekind domain](../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), for conjugation permuting the prime factors of $p\mathcal{O}_K$
- [Kronecker symbol with a prime denominator](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-sym-prime.md)
- [Kronecker symbol at a prime](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-at-prime.md)
- [Kronecker symbol at two](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/kronecker-at-two.md)

## Sources

- F. Keune, *Number Fields*, Radboud University Press, Nijmegen (2023, version 2023-01), open access,
  <https://doi.org/10.54195/IPVU4488>: Theorem 1.9 (integers of a quadratic number field, with the proof followed here) and Example 1.44
  ($\operatorname{disc} \mathbb{Q}(\sqrt{m})$ is $4m$ for $m \equiv 2, 3 \pmod 4$ and $m$ for $m \equiv 1 \pmod 4$); §3.1, Theorem 3.6
  (Kummer–Dedekind, p. 51) and Theorem 3.7 (pp. 52–53), the factorization of $p$ in $\mathbb{Q}(\sqrt{m})$.
