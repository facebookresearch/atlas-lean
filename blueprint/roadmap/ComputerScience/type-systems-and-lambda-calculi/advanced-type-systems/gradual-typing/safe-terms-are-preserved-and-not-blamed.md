# Safe terms are preserved and are not blamed

For every well-typed term $t$ of the [blame calculus](the-blame-calculus-and-its-subtyping-relations.md) and blame label $p$:

1. (preservation) if $t$ is [safe for $p$](terms-safe-for-a-blame-label.md) and $t \longrightarrow t'$, then $t'$ is safe for $p$;
2. (progress) if $t$ is safe for $p$, then $t \not\longrightarrow\ \Uparrow p$.

Together they give [the blame theorem](well-typed-programs-can-t-be-blamed.md): a term whose only cast labeled $p$ is a positive subtyping is safe for $p$, so no reduction
sequence from it ends in $\Uparrow p$.

## Depends on

- [Terms safe for a blame label](terms-safe-for-a-blame-label.md)

## Proof depends on

- [Type safety of the blame calculus](type-safety-of-the-blame-calculus.md)

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *European Symposium on Programming (ESOP 2009)*, LNCS 5502, 1–16, <https://doi.org/10.1007/978-3-642-00590-9_1>: Section 4, Propositions 9 (preservation of safe terms) and 10 (progress of safe terms).
