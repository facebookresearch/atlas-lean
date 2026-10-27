---
article_id: af_716deec46bfd4b6b9266f27f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.QPochhammer.jacobi_cube_euler_product_hasSum
---

# Jacobi Cube Euler Product

Jacobi's identity for the cube of Euler's product (concept
`jis_dep_557f7500b8f24447f106ea8c`): for `q : Complex` with `‖q‖ < 1`, the cube
`(qPochhammerInf q q hq) ^ 3` is the value of the unilateral weighted q-series with
`n`th term `(-1) ^ n * (2 * n + 1) * q ^ (n * (n + 1) / 2)`, stated as `HasSum`
so both convergence and the value are recorded.

Product side: the existing shared definition
`MetaMathlibExt.QPochhammer.qPochhammerInf a q hq = tprod (fun n : Nat => 1 - a * q ^ n)`
is used directly. Hence `qPochhammerInf q q hq = ∏ n : Nat, (1 - q ^ (n + 1))`,
i.e. the source product `(q;q)_∞` (whose factors start at index zero as
`1 - q ^ (n+1)`) indexed from the positive integers. The exponent
`n * (n + 1) / 2` is exact natural-number division (the triangular numbers).
Only the Jacobi equation is formalized here; the sibling Euler
pentagonal-number equation in the following displayed equation in the same
source lemma/alignment is a separate theorem.

## Depends on

- [Q Pochhammer Inf](../../../../../Analysis/MathlibExt/part-01/special-functions/part-02/qpochhammer/q-pochhammer-inf.md)

## Proof depends on

- [Q Pochhammer Inf Raw](../../../../../Analysis/MathlibExt/part-01/special-functions/part-02/qpochhammer/q-pochhammer-inf-raw.md)
- [Coeff jacobi Cube Series eq zero](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-01/partition/ramanujan-partition-congruence/coeff-jacobi-cube-series-eq-zero.md)
- [Coeff jacobi Cube Series triangle](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-01/partition/ramanujan-partition-congruence/coeff-jacobi-cube-series-triangle.md)
- [Jacobi Cube Series](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-01/partition/ramanujan-partition-congruence/jacobi-cube-series.md)
- [Pentagonal Series pow three](../../../../../Combinatorics/MathlibExt/part-01/enumerative/part-01/partition/ramanujan-partition-congruence/pentagonal-series-pow-three.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ModularForms.JacobiTheta.JacobiCubeEulerProduct](../../../../../../sources/v2/MathlibExt.md)
- Robson da Silva and James A. Sellers, "Parity Considerations for the Mex-Related Partition Functions of Andrews and Newman", `https://cs.uwaterloo.ca/journals/JIS/VOL23/Sellers/sellers52.tex`, lines 150-161 (equation `Jacobi` of the lemma; Eq. (1.3.24) of Berndt). Source id `jis_source_c8d2bdc54ead009b5569c3616402b81a56ef19629d00d9d0fe39346ee042bd4b`, source SHA-256 `c8d2bdc54ead009b5569c3616402b81a56ef19629d00d9d0fe39346ee042bd4b` (text-span SHA-256 `147b68447ae1625d8c453ed0ee55d501bc4846b4a7dd7ba33976e546224456e4`).
