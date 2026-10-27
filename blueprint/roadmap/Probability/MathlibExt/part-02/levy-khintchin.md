---
article_id: af_1988b46cc5c861e85a0f44dc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.levy_Khintchin
---

# Levy Khintchin

Lévy–Khintchin representation: a law `μ` on `ℝ` is infinitely divisible
iff its characteristic function has the drift–Gaussian–jump form with a drift
`γ`, a Gaussian coefficient `σ ≥ 0`, and a Lévy measure `ν` with `ν {0} = 0`
and `∫⁻ x, min 1 (x ^ 2) ∂ν < ∞`.

Proof: The reverse implication uses compound Poisson approximation plus Lévy continuity; the
forward implication uses a distinguished logarithm, canonical measures, and Prokhorov compactness.
For the equivalence, see William Feller, *An Introduction to Probability Theory and Its
Applications*, vol. II, Theorem XVII.2.1.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.LevyKhintchin](../../../../sources/v2/MathlibExt.md)
- Ken-iti Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge Studies in Advanced Mathematics 68, Cambridge University Press (1999), Theorem 8.1, pp. 37–38, ISBN 978-0-521-55302-5. <https://books.google.com/books?vid=ISBN9780521553025&jscmd=SearchWithinVolume2&q=Theorem+8.1> Scope: restricts Sato Theorem 8.1 (stated for `ℝ^d`) to `ℝ`, and formalizes only the existence direction (i), omitting uniqueness of the generating triplet (ii). The jump integrand uses the hard truncation `x * 1_{|x| ≤ 1}`, which is an equivalent convention to Sato's `x / (1 + |x|^2)` after reparameterizing the drift `γ`.
