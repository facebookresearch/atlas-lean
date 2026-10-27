---
article_id: af_ad4a8ba9dbcae32769eccb81
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.stirling_bell_polynomial_connection_pair
---

# Stirling bell polynomial connection pair

The generalized Laguerre polynomial `L_{n,r}(x)` expressed through signless
Stirling numbers of the first kind and Bell polynomials, together with the
inverse relation using Stirling numbers of the second kind:
`L_{n,r}(x) = ∑_k ∑_j [n,k] C(k,j) (αr)^{k-j} β^j B_j(x)` and
`∑_k (-1)^{n-k} S(n,k) L_{k,r}(x) = ∑_k C(n,k) (αr)^{n-k} β^k B_k(x)`,
where `B_j(x) = ∑_l S(j,l) x^l` and
`L_{n,r}(x) = ∑_k (1/k!) ∑_j (-1)^{k-j} C(k,j) (αr+βj)^{\overline{n}} x^k`.

It follows from `stirling_bell_polynomial_connection_pair_general`; the hypothesis `hβ` is
unused and keeps the source's shape.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Stirling bell polynomial connection pair general](stirling-bell-polynomial-connection-pair.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.StirlingBellPolynomialConnection](../../../../../../../sources/v2/MathlibExt.md)
- Mark Shattuck, "Combinatorial Properties of a Generalized Class of Laguerre Polynomials," Journal of Integer Sequences 24 (2021), Article 21.2.1, Theorem (label `eqnpair`), equations (labels `eqnpaire1`) and (`eqnpaire2`), lines 330–339, https://cs.uwaterloo.ca/journals/JIS/VOL24/Shattuck/shattuck24.tex
