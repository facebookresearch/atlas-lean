---
article_id: af_4446b74b11a3cd7459b7f7dc
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsLaplaceQFamily
---

# Laplace QPolynomial

Specification of a Laplace Q-polynomial family `Q` companion to a supplied
P-family `P`. The clause is `Q 0 = 1` and, for every `k ≥ 1`,
`Q k = P k + derivative (Q (k - 1))` together with
`Q (k + 1) = X * Q k + (k + 1) • Q (k - 1)`.
Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998.
Frozen source https://cs.uwaterloo.ca/journals/JIS/VOL19/Kreinin/kreinin4.tex,
bytes/chars 13284..13748, lines 306..315.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.LaplaceQPolynomial](../../../../sources/v2/MathlibExt.md)
