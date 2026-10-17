---
article_id: af_6511af908110c5fb74cc49ef
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.EfronStein.efron_stein_finite_iid
---

# Efron stein finite iid

Expected sum of squared differences under independent resampling of each coordinate.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Efron stein finite iid general](efron-stein-finite-iid-general.md)

## Sources

- [MathlibExt, MathlibExt.Probability.EfronStein](../../../../../sources/v2/MathlibExt.md)
- B. Efron and C. Stein, "The Jackknife Estimate of Variance", Annals of Statistics 9 (1981), DOI 10.1214/aos/1176345462. It follows from `efron_stein_finite_iid_general`; the instance `[DecidableEq α]` is unused and keeps the source's shape. Proves `Wanted` entry `efron_stein_finite_iid`.
