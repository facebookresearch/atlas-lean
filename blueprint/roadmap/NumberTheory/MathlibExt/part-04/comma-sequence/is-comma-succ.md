---
article_id: af_201009e636c0c47b7062ca5a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsCommaSucc
---

# Is Comma Succ

Comma-successor relation: `m = n + b * (n % b) + y.val` for a candidate `y`,
minimal over every smaller digit, so smallest `y` is exactly the lexicographically
earliest next value (source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Comma Candidate](is-comma-candidate.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.CommaSequence](../../../../../sources/v2/MathlibExt.md)
