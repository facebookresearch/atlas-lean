---
article_id: af_78ca9befc429d66e15934a1c
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.WirsingConstant.IsEigenvalue
---

# Is Eigenvalue

An eigenvalue of the GKW operator, with eigenfunction continuous and
nonzero on `[0, 1]` (hence bounded there, recorded explicitly). This
continuous model is *not* the source's spectral space: it admits
eigenvalues that the holomorphic theory excludes (for example `1/3`,
from eigenfunction lifts under inversion), so it is kept only as a
pointwise model exhibiting the dominant eigenvalue `1` below. The
Wirsing constant itself is defined over holomorphic eigenfunctions at
`IsHolomorphicEigenvalue`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gkw Term](gkw-term.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.WirsingConstant](../../../../../sources/v2/MathlibExt.md)
