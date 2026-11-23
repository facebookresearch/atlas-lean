# Fingerprinting with irreducible polynomials

Rabin's fingerprinting: a bit string is identified by its residue modulo a randomly chosen
irreducible polynomial of degree $k$ over $\mathbb{Z}_2$. The error analysis is a count: a nonzero
polynomial of degree $D$ has at most $D/k$ irreducible factors of degree $k$, while there are
$(2^k - 2)/k$ irreducible polynomials of prime degree $k$ to choose from.

- [Monic irreducible polynomials of prime degree over Z/pZ](ncard-monic-irreducible-mul-of-prime.md)
- [Monic irreducible polynomials of prime degree over Z2](ncard-monic-irreducible-zmod-two-of-prim.md)
- [At most deg H / k irreducible factors of degree k](card-filter-dvd-mul-le-nat-degree.md)
- [The fingerprint error count](card-filter-exists-dvd-mul-le-sum-nat-de.md)

## Related topics

- [Rabin–Karp algorithm](../../../ComputerScience/string-algorithms/rabin-karp-algorithm/README.md): string matching with fingerprints modulo an integer, here in
  the deterministic form that checks every fingerprint match, so it needs no error bound.
- [Searching for irreducible polynomials over GF(2)](../searching-for-irreducible-polynomials-over-gf-2/README.md):
  a deterministic way to find one modulus of each degree, where Rabin draws a random one.
- Schwartz–Zippel lemma: the dual counting bound, for a random evaluation point instead of a random modulus.
