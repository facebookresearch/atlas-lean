# Goldwasser–Micali's Lemma 2

Let $p \ne q$ be primes and let $c$ be a unit modulo $pq$. Then $c$ is a square modulo $pq$ if and only
if $c^{\lfloor p/2 \rfloor} \equiv 1 \pmod p$ and $c^{\lfloor q/2 \rfloor} \equiv 1 \pmod q$. For odd
$p$, $\lfloor p/2 \rfloor = (p - 1)/2$, which is the exponent of Euler's criterion; the statement also
holds when one of the primes is $2$.

## Informally uses

- [Square units](is-square-units-iff.md): residuosity among units equals residuosity in the ring.
- [Squares in a product](is-square-prod-iff.md): applied to the Chinese remainder isomorphism
  $\mathbb{Z}/pq \cong \mathbb{Z}/p \times \mathbb{Z}/q$, before Euler's criterion in each factor.

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4, Lemma 2 and its proof: a residue is a square modulo $N = p_1 p_2$ exactly
  when it is a square modulo $p_1$ and modulo $p_2$, and modulo a prime $p$ it is a square exactly when
  its $(p-1)/2$-th power is $1$.
