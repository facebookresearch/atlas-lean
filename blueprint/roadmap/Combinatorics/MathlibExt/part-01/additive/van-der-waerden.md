---
article_id: af_2dc51c222d86670eab37ef61
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.vanDerWaerden
---

# Van Der Waerden AP

Van der Waerden's theorem: for positive integers `r` (colors) and `k`
(progression length), there exists `N = W(r, k)` such that every `r`-coloring
of `{1, ..., N}` contains a monochromatic `k`-term arithmetic progression
`a, a + d, ..., a + (k - 1) * d` with `d ≥ 1`.

Proof: Apply the Hales-Jewett theorem to digit-sum encodings of words over `Fin k`, so a
combinatorial line becomes an arithmetic progression. This follows the standard derivation in
Graham, Rothschild, and Spencer, *Ramsey Theory*, Section 2.3, from van der Waerden (1927).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.VanDerWaerdenAP](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Van_der_Waerden%27s_theorem
