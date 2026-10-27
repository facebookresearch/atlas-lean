---
article_id: af_3f7e4316a14651da11321ce6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.eval_qrDowlingPolynomial_whitneySecond
---

# Eval qr Dowling Polynomial whitney Second

The `(q, r)`-Dowling polynomial of the `(q, r)`-Whitney numbers of the second kind expands
through any family `qStirlingSecond` with the recurrence of the `q`-Stirling numbers of the
second kind: `D(n,x) = ∑ k, C(n,k) * r ^ (n - k) * ∑ j, m ^ (k - j) *
qStirlingSecond k j * x ^ j`.

## Depends on

- [Q Brack](../qrwhitney-numbers/q-brack.md)
- [Whitney Second](../qrwhitney-numbers/whitney-second.md)
- [Qr Dowling Polynomial](../../../../../../NumberTheory/MathlibExt/part-10/qrdowling-polynomial/qr-dowling-polynomial.md)

## Proof depends on

- [Whitney Second eq sum q Stirling Second](whitney-second-eq-sum-q-stirling-second.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.QRDowlingQStirlingExpansion](../../../../../../../sources/v2/MathlibExt.md)
- M. M. Mangontarum, *Some Theorems and Applications of the (q,r)-Whitney Numbers*, Journal of Integer Sequences 20 (2017), Article 17.2.5, theorem equation `genpriv`, lines 782-789, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>.
