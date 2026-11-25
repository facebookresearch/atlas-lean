# Resolvent mul resolvent

The first resolvent identity in the orientation used by the classical
multiplicativity proof.  The order of the two resolvent factors is retained,
so the statement applies to noncommutative Banach algebras.  The inequality
`z ≠ ζ` is essential because Mathlib's scalar inverse is totalized.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem resolvent_mul_resolvent {a : A} {z ζ : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hζ : ζ ∈ resolventSet ℂ a)
    (hzζ : z ≠ ζ) :
    resolvent a z * resolvent a ζ =
      (ζ - z)⁻¹ • (resolvent a z - resolvent a ζ)
```
