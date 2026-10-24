---
declaration: def
origin: cited
statement: formalized
lean: Int.wilsonQuotient
---

# Wilson Quotient

Wilson quotient `W(p) = ((p-1)! + 1) / p` as an integer.

For a prime `p` the quotient is integral by Wilson's theorem `p ∣ (p-1)! + 1`
(`ZMod.wilsons_lemma`). The definition is total on `ℕ`; the source domain
"odd prime" from Matsuno 2607.10106, ll. 44–51 is imposed as hypotheses where
needed in the lemmas, not in the type of the definition.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.WilsonQuotient](../../../../../sources/v2/MathlibExt.md)
