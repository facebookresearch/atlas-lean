---
article_id: af_3e1e7ec1f0ffcd032a417d92
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsCommaCandidate
---

# Is Comma Candidate

Finite candidate digit for the generalized comma step: with `x = n % b`
the least significant digit, `m = n + b * (n % b) + y.val` is the next value
and `y` is its most significant digit
(source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Comma Msd](comma-msd.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.CommaSequence](../../../../../sources/v2/MathlibExt.md)
