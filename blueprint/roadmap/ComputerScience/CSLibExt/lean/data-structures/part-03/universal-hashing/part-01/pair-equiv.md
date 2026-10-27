---
article_id: af_4c7be1101055f731077387f4
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.UniversalHashing.pairEquiv
---

# Pair Equiv

The core bijection of the CLRS counting argument. For fixed distinct keys `x ≠ y` in
the field `ZMod p`, solving the linear system `a * x + b = r`, `a * y + b = s` gives
`a = (r - s) / (x - y)` and `b = r - a * x`; this inverts `pairMap`. Hence the indices
`(a, b)` with `a ≠ 0` are in bijection with the ordered pairs `(r, s)` with `r ≠ s`.

## Depends on

- [Mod Prime Index](mod-prime-index.md)

## Proof depends on

- [Pair Map](pair-map.md)
- [Pair Map fst ne snd](pair-map-fst-ne-snd.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing](../../../../../../../../sources/v2/CSLibExt.md)
