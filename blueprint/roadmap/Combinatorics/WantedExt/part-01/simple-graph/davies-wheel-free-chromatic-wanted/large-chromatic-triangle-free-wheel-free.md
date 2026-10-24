---
article_id: af_d70de1b2fe31b3e69b98e5dc
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted.largeChromaticTriangleFreeWheelFree
---

# Large Chromatic Triangle Free Wheel Free

The complete finite-graph existence assertion in Davies's Corollary 2.
The witnesses are finite simple graphs, enumerated by `Fin n`. Triangle-freeness
is Mathlib's `CliqueFree 3`; its extended-natural chromatic number is finite
for these vertex types. The threshold is any positive integer.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Wheel Free](wheel-free.md)

## Sources

- [WantedExt, WantedExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted](../../../../../../sources/v2/WantedExt.md)
- Davies, arXiv:2104.05907v3, Corollary 2, page 1; the finite constructions are given on pages 5 and 6, https://arxiv.org/pdf/2104.05907v3.
