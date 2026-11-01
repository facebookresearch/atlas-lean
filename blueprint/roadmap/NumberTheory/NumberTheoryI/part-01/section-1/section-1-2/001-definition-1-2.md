---
article_id: af_c4555240c699e1d2fd30ab11
declaration: abbrev
origin: cited
statement: formalized
lean: FieldAbsoluteValue
---

# Definition 1.2

An absolute value on a field $k$ is a map $|\cdot| \colon k \rightarrow \mathbb{R}_{\geq 0}$ such that for all $x, y \in k$ the following hold:
1. $|x|=0$ if and only if $x=0$;
2. $|xy| = |x| \cdot |y|$;
3. $|x+y| \leq |x|+|y|$.
If the stronger condition
4. $|x+y| \leq \max(|x|,|y|)$
also holds, then the absolute value is nonarchimedean; otherwise it is archimedean.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 1.2](../../../../../../sources/v1/NumberTheoryI.md)
