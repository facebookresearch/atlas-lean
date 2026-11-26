# Riesz Functional Calculus Alg Hom apply

The bundled algebra homomorphism has the stated functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculusAlgHom_apply (a : A)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculusAlgHom a f = rieszFunctionalCalculus a f
```
