# The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs

Let $\mathrm{PKE}_1$ be deterministic and $H$ a hash function into a key space $K$. The *explicit-rejection* KEM $U^{\perp}[\mathrm{PKE}_1, H]$ encapsulates by sampling $m \leftarrow M$ and returning $c = \mathrm{Enc}_1(pk, m)$ and $K = H(m, c)$; decapsulation returns $H(m', c)$ for $m' = \mathrm{Dec}_1(sk, c)$, or $\bot$ if $m' = \bot$. The *implicit-rejection* KEM $U^{\not\perp}$ additionally stores a uniform secret seed $s$ in the secret key and on failure returns the pseudorandom key $H(s, c)$ instead of $\bot$. The Fujisaki–Okamoto KEMs are the compositions

$$
\mathrm{FO}^{\perp} = U^{\perp} \circ T, \qquad \mathrm{FO}^{\not\perp} = U^{\not\perp} \circ T .
$$

ML-KEM is $\mathrm{FO}^{\not\perp}$-style: it hashes the public key into the derivation, $(K, r) = G(m \,\Vert\, H(ek))$, re-encrypts with $r$ during decapsulation, and on mismatch returns $J(z \,\Vert\, c)$ for a secret seed $z$.

## Depends on

- [The derandomizing transform $T$](transform-t.md)
- [Key-encapsulation mechanism](../../key-encapsulation-and-hybrid-encryption/kemscheme.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
