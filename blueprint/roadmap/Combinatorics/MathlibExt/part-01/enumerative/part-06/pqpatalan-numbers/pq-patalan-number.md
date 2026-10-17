---
article_id: af_20b0cd856279d0ecfa5d5586
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.pqPatalanNumber
---

# Pq Patalan Number

`(p,q)`-Patalan numbers: `b(n) = -p ^ (2 * n + 1) * binom{n - q / p}{n + 1}`.

The parameters are taken as a `PQPatalanParams` bundle, hence satisfy
`p > 1` and `0 < q < p`, and `n` is a natural number index. The binomial
factor uses a fractional upper argument. Stable source identifiers:
concept `jis_sem_46b7b4c899beee2d386fd944`,
statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`.

## Depends on

- [PQPatalan Params](pqpatalan-params.md)

## Proof depends on

- [Patalan Generalized Binomial](patalan-generalized-binomial.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PQPatalanNumbers](../../../../../../../sources/v2/MathlibExt.md)
