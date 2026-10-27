---
article_id: af_9069d9b3880587e6609af975
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.digital_binomial_theorem
---

# Digital binomial theorem

Digital binomial theorem: `(x + y)` to the binary digit sum of `n`
expands as the sum over `m ≤ n` with `(m, n - m)` carry-free of
`x ^ s(m) * y ^ s(n - m)`, where carry-free means the binary digit
sums add up.

Carry-free is encoded as `s(m) + s(n - m) = s(n)`, which the source
notes (line 114) is equivalent to binary addition without carries;
this is also equivalent to `m` being a bitwise submask of `n`.
Verified computationally for `n = 0..63` over four integer pairs.

## Depends on

- [Bin Digit Sum](bin-digit-sum.md)

## Proof depends on

- [Digital binomial theorem general](digital-binomial-theorem-general.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.DigitalBinomialTheorem](../../../../../../../sources/v2/MathlibExt.md)
- Hieu D. Nguyen, "A Generalization of the Digital Binomial Theorem," Journal of Integer Sequences 18 (2015), Article 15.5.7, Theorem (label th:digital-binomial-theorem), equation (label eq:digital-binomial-theorem-carry-free), lines 107–113, https://cs.uwaterloo.ca/journals/JIS/VOL18/Nguyen/nguyen6.tex
