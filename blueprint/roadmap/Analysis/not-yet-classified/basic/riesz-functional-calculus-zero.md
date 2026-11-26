# Riesz Functional Calculus zero

The zero holomorphic germ has Riesz value zero.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_zero (a : A) :
    rieszFunctionalCalculus a 0 = 0
```
