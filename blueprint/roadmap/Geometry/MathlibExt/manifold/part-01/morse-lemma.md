---
article_id: af_31bd08cbbc41376eaec8f45e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.MorseLemmaWanted.morse_lemma
---

# Morse Lemma

If `f : ℝⁿ → ℝ` is `C^∞` with `fderiv ℝ f 0 = 0` and nondegenerate Hessian at `0`, then there
exist `k ≤ n`, a `C^∞` local diffeomorphism `φ` at `0` with `φ 0 = 0`, and open `U ∋ 0` such that
`f x = f 0 + Q_k (φ x)` on `U`, where `Q_k = morseQuadratic k n`. Source: J. Milnor, Morse Theory,
Ann. of Math. Studies 51 (1963) Lemma 2.2; M. Hirsch, Differential Topology; J. Lee, Intro to
Smooth Manifolds, 2nd ed., Morse lemma; Lean states Euclidean origin finite-dimensional
specialization with corrected nondegeneracy grouping `(∀ w, (fderiv (fderiv f) 0 v) w = 0) → v =
0`.

## Depends on

- [Morse Quadratic](morse-theory/morse-quadratic.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.MorseLemma](../../../../../sources/v2/MathlibExt.md)
