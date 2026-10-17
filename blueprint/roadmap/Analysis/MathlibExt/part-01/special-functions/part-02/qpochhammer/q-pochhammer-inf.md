---
article_id: af_7485a6f4d3288f89d10805ba
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.QPochhammer.qPochhammerInf
---

# Q Pochhammer Inf

Complex infinite q-Pochhammer symbol `(a;q)_∞`, restricted to the unit disk.

Source `2607.10576:D01` / `2608.13818:D02` jointly define
`(a;q)_∞ := ∏_{j=0}^{∞} (1 - a·q^j)` for complex `a, q` with `‖q‖ < 1`.
On this domain the value agrees with the raw product `qPochhammerInfRaw a q`,
while the hypothesis `hq` makes it impossible to silently evaluate at an
out-of-domain `q`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Q Pochhammer Inf Raw](q-pochhammer-inf-raw.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.QPochhammer](../../../../../../../sources/v2/MathlibExt.md)
