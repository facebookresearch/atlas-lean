---
article_id: af_d972cfd3e78ed66f33d1fc01
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.boxProd_tiling_card_eq_fib_mul_pell
---

# Box Prod tiling card eq fib mul pell

The number of domino tilings, as perfect matchings, of `W_4 □ P_{n-1}`
equals `f_n * p_n` for `n ≥ 2`.

`W_4` is `K_4` minus one edge; `P_n` is the path graph on `n` vertices;
`□` is the Cartesian product (the paper's `×`, following Faase).
Fibonacci `f_1 = f_2 = 1` (lines 91–94) is `Nat.fib`; the Pell factor
`p_1 = 1, p_2 = 2` (lines 96–99) is encoded inline by `Nat.rec` on pairs
with base `(0, 1)`, so `p_0 = 0, p_1 = 1, p_2 = 2`.
The paper's values `c_2 = 2, c_3 = 10, c_4 = 36` match `fib * pell`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Box Prod tiling card eq fib mul pell Number](box-prod-tiling-card-eq-fib-mul-pell-num.md)
- [Pell Number Sequence](../../../../../../NumberTheory/MathlibExt/part-08/pell-number.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.W4PathDominoTilings](../../../../../../../sources/v2/MathlibExt.md)
- James A. Sellers, "Domino Tilings and Products of Fibonacci and Pell Numbers," Journal of Integer Sequences 5 (2002), Article 02.1.2, Theorem (label mainresult), lines 105–108, https://cs.uwaterloo.ca/journals/JIS/VOL5/Sellers/sellers4.tex
