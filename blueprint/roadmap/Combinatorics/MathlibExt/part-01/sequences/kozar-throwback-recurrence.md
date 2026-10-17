---
article_id: af_236151cb81a72f5622500412
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.kozar_throwback_recurrence
---

# Kozar Throwback Recurrence

Kozar's conjecture for OEIS A357081: every value `n ≥ 3` recurs as the
leader `T k` for arbitrarily large iteration counts `k` (unbounded/infinite
recurrence). Here `throwbackStep` exactly moves the leader to index `Y 0`,
and `T k` is the leader after `k` iterations starting from `X i = i + 3`.
This is no longer open: Dribus et al. prove the stronger general theorem for
every sequence of distinct positive integers. Source: Jesiah Darnell and
Benjamin F. Dribus, “Throwback Sequences of Positive Integers”,
`https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.tex`
(full SHA-256 `91dac9c7d7f6c550c7644258f70d07a03c43f6c7ffc28235addd4dc7598ac86b`);
conjecture/introduction lines 71–80 (span SHA-256
`70d48f104dceb3101445c02233f446b984d48e2f9843a23a7ea661e55741e449`); exact
throwback definition lines 98–103 (span SHA-256
`6c3a467d42a32e27785634c47c0c2e0ab98cbb5c1b8c8170b0f23ad6d6dfeefc`); general
recurrence theorem and proof lines 124–137 (span SHA-256
`fae94ddbaa20aa3fee2d0efef1edd5ee1a73dc13ba62c6053c969a09e915abb5`);
concept id `jis_grounded_4375195697bd0ce6cf205efc`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Sequences.KozarThrowbackRecurrence](../../../../../sources/v2/MathlibExt.md)
