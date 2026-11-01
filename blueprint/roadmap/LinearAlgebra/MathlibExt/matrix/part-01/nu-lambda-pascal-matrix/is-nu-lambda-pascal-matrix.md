---
article_id: af_6f4376a25c97d62887d2c740
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsNuLambdaPascalMatrix
---

# Is Nu Lambda Pascal Matrix

Nu,lambda-Pascal matrix with coefficients (concept `jis_sem_48e0bb143520a73f6b828a27`,
source statement `jis_445c3486a9ca32dba0e8a333`): zero-extended `2n × 2n`
skew-symmetric matrix over `ℂ` given by the corner value, the last-column sum,
and the interior recurrence. The unused binder `_hn : 0 < n` records the source
hypothesis `n > 0` licensing the zero-based positions `2 * n - 2` and
`2 * n - 1`.

The API deliberately also permits `N = 0`; then the beta-index is empty and
the last-column sum is zero. The source's intended coefficient families have
`N > 0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.NuLambdaPascalMatrix](../../../../../../sources/v2/MathlibExt.md)
