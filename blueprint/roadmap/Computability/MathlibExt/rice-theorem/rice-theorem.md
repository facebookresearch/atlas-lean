---
article_id: af_2998445b71543f2400c4b94b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.rice_theorem
---

# Rice theorem

Rice's theorem (rice-s1): any nontrivial semantic index set for an acceptable
numbering of partial computable functions is undecidable. Codes are `ℕ` via the
acceptable enumeration `φ` with computable universal evaluation and the s-m-n
property; extensional equivalence is `∀ n, φ a n = φ b n`; nontriviality means the
index set is both inhabited and non-universal; undecidability is nonexistence
of a computable decider.

Proof: The standard argument first derives Kleene's recursion theorem for the acceptable
numbering, then diagonalizes a putative decider, following Rice (1953), Rogers §11.2, and
Soare II.3.1.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Acceptable Numbering fixed point](acceptable-numbering-fixed-point.md)

## Sources

- [MathlibExt, MathlibExt.Computability.RiceTheorem](../../../../sources/v2/MathlibExt.md)
- H. G. Rice, *Classes of recursively enumerable sets and their decision problems*, Transactions of the American Mathematical Society 74(2) (1953), 358-366.
