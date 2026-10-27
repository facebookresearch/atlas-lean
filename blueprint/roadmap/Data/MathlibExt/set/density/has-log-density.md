---
article_id: af_33db0aa44a3340a4c0845fd5
declaration: def
origin: cited
statement: formalized
lean: Set.Set.HasLogDensity
---

# Has Log Density

A set `A` of natural numbers has logarithmic density `d` if the sequence
$(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
Logarithmic density is a weaker notion than natural density: if a set has natural density `d`,
then it also has logarithmic density `d`, but the converse is false.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Data.Set.Density](../../../../../sources/v2/MathlibExt.md)
