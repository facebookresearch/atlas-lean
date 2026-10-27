---
article_id: af_a11b49bbd67e80ad016f2159
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.nim_sum_eq_zero_iff_last_eq_xor_fold
---

# Nim Sum Last Pile

A Nim position with preceding piles `preceding` and last pile `last` has
nim-sum zero iff `last` equals the xor of `preceding`.

This is only the nim-sum identity behind the source's corollary. The corollary
itself characterizes P-positions; its game-theoretic content (that nim-sum-zero
positions are exactly the P-positions) is Bouton's theorem,
`MetaMathlibExt.BoutonNim.bouton_nim_p_positions` in
`MathlibExt/GameTheory/BoutonNim.lean`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GameTheory.NimSumLastPile](../../../sources/v2/MathlibExt.md)
- Tanya Khovanova and Joshua Xiong, "Nim Fractals," Journal of Integer Sequences 17 (2014), Article 14.7.8, Corollary (label thm:ppos), lines 163–165, https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex Proves `Wanted` entry `nim_ppos_iff_last_eq_xor_fold`, renamed because it states no P-position predicate.
