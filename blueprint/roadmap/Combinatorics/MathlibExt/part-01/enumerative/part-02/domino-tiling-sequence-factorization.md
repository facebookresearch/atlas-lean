---
article_id: af_fa9724d4e158446cbf3ce799
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.domino_tiling_sequence_factorization
---

# Domino Tiling Sequence Factorization

The domino tiling counting sequence `d` (A003775, tilings of
`P_5 × P_{2n-2}`) factors as the product of a second-order auxiliary
sequence `g` (A004253) and odd-indexed Fibonacci numbers.

`d` satisfies the fourth-order recurrence (label brecur) with
`d_1 = 1, d_2 = 8, d_3 = 95, d_4 = 1183`; `g` satisfies
`g_{n+2} = 5 g_{n+1} - g_n` (label k3stuff); `h_n = f_{2n-1}`
is `Nat.fib (2 * n - 1)`. Distinct from the same paper's main
theorem on `W_4 × P_{n-1}` tilings equaling `f_n p_n`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.DominoTilingSequenceFactorization](../../../../../../sources/v2/MathlibExt.md)
- James A. Sellers, "Domino Tilings and Products of Fibonacci and Pell Numbers," Journal of Integer Sequences 5 (2002), Article 02.1.2, second Theorem (`d_n = g_n h_n`), lines 153–154, with `d` defined at lines 146–150 and `g` at line 164, https://cs.uwaterloo.ca/journals/JIS/VOL5/Sellers/sellers4.tex
