---
article_id: af_e6ceea312a9ceb2758d0b8a5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.favard_iff
---

# Favard Iff

Canonical Favard iff endpoint for monic polynomial sequences.

The zero-based `n + 2` recurrence form below is exactly equivalent to the source's
`n ≥ 1` form. The forward direction is `favard_forward`; the reverse direction is proved
here.

## Depends on

- [Formal Orthogonality](is-formally-orthogonal.md)

## Proof depends on

- [Favard Forward](favard-forward.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Polynomial.FavardIff](../../../../sources/v2/MathlibExt.md)
- Paul Barry, "Riordan Arrays, Orthogonal Polynomials as Moments, and Hankel Transforms," Journal of Integer Sequences 14 (2011), Article 11.2.2. Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry1/barry97r2.tex Actual Favard theorem: lines 346–352. Source SHA-256: `390bd7d75055d92085e8cd502df8b435fc1e45b1bbf8920038605d3fa1d1fe80`. Theorem-span SHA-256: `636f9c2d5233070dc92150b854d33ace8d01e246fc385d8a80fee32dc8f218ab`. Stable concept ID: `jis_grounded_fa98ab71d0d207da0e58a1fe`.
