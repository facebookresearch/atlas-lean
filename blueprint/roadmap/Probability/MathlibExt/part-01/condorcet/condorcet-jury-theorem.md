---
article_id: af_8a09849293ce6dabb43b04d0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.condorcet_jury_theorem
---

# Condorcet jury theorem

Condorcet's jury theorem (statement ID `condorcet-s1`): n independent voters
each correct with probability `p > 1/2`, with votes modeled as Bernoulli trials;
the majority vote, via a `Finset.card` threshold, is correct with probability
tending to 1 as `n → ∞` and exceeding `p` for every odd `n > 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.Condorcet](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Condorcet%27s_jury_theorem. Proves `Wanted` entry `condorcet_jury_theorem`.
