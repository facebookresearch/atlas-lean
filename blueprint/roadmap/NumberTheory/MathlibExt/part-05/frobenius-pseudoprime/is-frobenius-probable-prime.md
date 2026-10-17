---
article_id: af_0f30bbd938b4a7380b68eb27
declaration: def
origin: cited
statement: formalized
lean: Nat.IsFrobeniusProbablePrime
---

# Is Frobenius Probable Prime

Frobenius probable prime (pseudo1.tex lines 713-741).
`f` is monic over the integers; degree and discriminant are `f.natDegree`
and `f.discr`. `n` is odd, greater than one, and coprime to the natural
absolute value of `f.eval 0 * f.discr`. All algorithm polynomials live over
`ZMod n`: `fs 0` is the coefficientwise reduction of `f`; each `F i` is a
greatest common monic divisor of `X ^ (n ^ i) - X` and `fs (i - 1)` with exact
factorization `fs (i - 1) = F i * fs i`; the stage ends with `fs f.natDegree = 1`.
The Frobenius step asks `F i ∣ (F i).comp (X ^ n)` for `2 ≤ i ≤ d`.
With quotient witnesses `q`, each even `i` satisfies `natDegree (F i) = i * q i`,
and the Jacobi step asks `(-1) ^ S = jacobiSym f.discr n` where `S` sums
`q i` over the even indices, zero elsewhere.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Greatest Common Monic Divisor](is-greatest-common-monic-divisor.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.FrobeniusPseudoprime](../../../../../sources/v2/MathlibExt.md)
