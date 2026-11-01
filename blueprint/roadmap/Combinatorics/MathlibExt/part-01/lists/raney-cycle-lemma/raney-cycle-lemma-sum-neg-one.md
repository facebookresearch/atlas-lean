---
article_id: af_eb7bb05a26a1efdc3e74a875
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.raney_cycle_lemma_sum_neg_one
---

# Raney cycle lemma sum neg one

Raney's cycle lemma in the sum-minus-one form: for a finite list `a : List Int`
with every entry at least `-1` and total sum `-1`, there exists exactly one rotation
index whose proper prefixes all have nonnegative sum. Lean's zero-based left rotation
is a bijective reindexing of the source's cut after `a_r`; `t < a.length` ranges over
every proper prefix, with `t = 0` giving the true empty-prefix condition.

Grounded record: `jis_grounded_7df8f01cf825a78240bfc1d3`.
Concept: `jis_dep_4e5e1a90d8c5f1fdb136c3c0`.
Frozen source: `https://cs.uwaterloo.ca/journals/JIS/VOL24/Haupt/haupt4.tex`, lines 804-807.
Source file SHA-256: `1b412146e9dba7d9302d274268baf3e35239b8369473faf57f086f918e3b66af`.
Exact span SHA-256: `c5a3ab122e3bf8a75f6f8c7999cd1e20f508115ff91a537497e61ab7c1359b23`.
Corrected counts: 3 mentions / 1 paper / 1 proof use.

The lower bound `hlower` is not needed; see `raney_cycle_lemma_sum_neg_one_general`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Raney cycle lemma sum neg one general](raney-cycle-lemma-sum-neg-one-general.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Lists.RaneyCycleLemma](../../../../../../sources/v2/MathlibExt.md)
