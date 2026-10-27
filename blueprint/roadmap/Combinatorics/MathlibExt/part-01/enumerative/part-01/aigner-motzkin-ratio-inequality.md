---
article_id: af_b906885d12d99281eb5267a3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.aigner_motzkin_ratio_inequality
---

# Aigner Motzkin Inequality

Aigner's ratio inequality for Motzkin numbers (equation (11)).

Paper: Takashi Agoh and Horst Alzer, "Mean Value Inequalities for Motzkin Numbers",
Journal of Integer Sequences 24 (2021), Article 21.6.8.

Motzkin-number definition, lines 89--107, span SHA-256
`25821864e9da743abcc457fc8eb6b4552118fe71e96860b9dcfccafd67265509`:
`M_r = ∑_{k=0}^{⌊r/2⌋} (1/(k+1)) * C(2k,k) * C(r,2k)`.
Aigner ratio inequality, lines 373--386, equation (11), span SHA-256
`c1aac7efaa47a655d6ec5700396a2da6d327480cb691be23c5438f68f4c54292`:
`(M_n - M_{n-1}) / (M_{n+1} - M_n) ≤ M_n / M_{n+1}` for `n ≥ 1`.
Source file SHA-256
`b4e1a1ea2e4c22d7d5ee39e09ccac420b7f09db9eeacc83d0023e1deacb051d6`.

Stable identifiers: queue item `jis_grounded_4ec4cac48d863b8ffa953aa1`,
record `jis_grounded_4ec4cac48d863b8ffa953aa1__aigner_motzkin_ratio_inequality`,
named dependency/concept `jis_dep_ed005189a28461a49aaf0092`.
Corrected occurrence accounting: 1 named mention / 1 paper / 0 proof uses.

Scope: this proves the complete selected theorem statement as a MathlibExt theorem,
not a prerequisite stage. The ratio form is kept as stated; it is not replaced
with a log-convexity reformulation. The Motzkin numbers are let-bound locally as
`M` with the integral Catalan factor `Nat.choose (2 * k) k / (k + 1)` and the
exact range `0 ≤ k ≤ floor(r/2)` via `Finset.range (r / 2 + 1)`; no new
Motzkin-number wrapper is introduced. Current formal-math has related generalized
Motzkin-path/Riordan objects but no exact reusable natural-valued Motzkin-number
API matching this source contract.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.AignerMotzkinInequality](../../../../../../sources/v2/MathlibExt.md)
- <https://cs.uwaterloo.ca/journals/JIS/VOL24/Alzer/alzer8.tex>.
