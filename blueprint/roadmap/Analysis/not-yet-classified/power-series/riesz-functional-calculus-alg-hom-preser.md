# Riesz Functional Calculus Alg Hom preserves Compact Open Seq Limits

The Riesz functional-calculus algebra homomorphism preserves sequential
compact-open limits on a common analytic neighborhood of the spectrum.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculusAlgHom_preservesCompactOpenSeqLimits
    (a : A) :
    PreservesCompactOpenSeqLimits a
      (rieszFunctionalCalculusAlgHom a).toNonUnitalAlgHom
```
