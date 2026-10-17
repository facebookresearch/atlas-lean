---
article_id: af_cf3ebc47c35f098d6c5aefa1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.wirtinger_inequality
---

# Wirtinger

Wirtinger's inequality for functions: a C1 function on `[0, π]` vanishing at the endpoints
satisfies `∫₀^π f² ≤ ∫₀^π (f')²`.

Proof: A Picone-type comparison. For `0 < c < 1` the weight `h x = -c * tan (c * (x - π / 2))` is
smooth on `[0, π]` with `h' + h ^ 2 = -c ^ 2`, so integrating
`f' ^ 2 = (f' - h * f) ^ 2 + (h * f ^ 2)' + c ^ 2 * f ^ 2` gives `c ^ 2 * ∫ f ^ 2 ≤ ∫ f' ^ 2`;
then let `c` tend to one.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.Wirtinger](../../../../../sources/v2/MathlibExt.md)
- G. H. Hardy, J. E. Littlewood, and G. Pólya, *Inequalities*, second edition, Cambridge University Press, 1952, §7.7 (the endpoint-zero form on `[0, L]`).
