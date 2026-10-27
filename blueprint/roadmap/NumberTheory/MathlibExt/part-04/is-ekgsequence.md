---
article_id: af_5e5722bed13f8437623256e8
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsEKGSequence
---

# EKGSequence

EKG sequence predicate (phrase `EKG sequence`, concept `jis_term_4d5aa413ec3ba8694ef806b3`).
Provenance: JIS source `hofman1.tex`, lines 99–100,
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Hofman/hofman1.tex>
(SHA-256 `1aa5911c072e187d31e51d722d7b2dbad3cf7e147ce4e01658e21a09105a2089`);
(SHA-256 `a0fe543083e8c48473cd3fa58df152f49aa99d5132f657fd7b0feb3f77c04243`)
(first terms `1, 2, 4, 6, 3, 9, 12, 8, 10, 5, ...` at lines 104-112).
Zero-based shift: source `a_1 = 1` is Lean `a 0 = 1`, source `a_2 = 2` is Lean `a 1 = 2`;
the recurrence at Lean `a (n + 2)` has previous term `a (n + 1)`.
Positive-candidate convention: every next term satisfies `0 < a (n + 2)`; zero is never permitted.
Unused-prefix meaning: `a (n + 2)` differs from every earlier value, i.e.
`∀ i, i < n + 2 → a i ≠ a (n + 2)`; the minimality quantifier uses the same prefix condition
`∀ i, i < n + 2 → a i ≠ m` for candidate `m`.
Gcd condition: `Nat.gcd (a (n + 1)) (a (n + 2)) > 1`.
Minimality meaning: `a (n + 2)` is the least positive unused candidate sharing a factor
greater than 1 with `a (n + 1)`, i.e. `∀ m, 0 < m → unused m → gcd > 1 → a (n + 2) ≤ m`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.EKGSequence](../../../../sources/v2/MathlibExt.md)
