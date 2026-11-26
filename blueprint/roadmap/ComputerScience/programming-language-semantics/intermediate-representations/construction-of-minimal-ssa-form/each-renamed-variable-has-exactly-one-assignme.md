# Each renamed variable has exactly one assignment

In the program produced by the renaming step of [translation to SSA form](translation-to-static-single-assignment-form.md), each new variable $V_i$ is the target of exactly one assignment.

**Proof.** The counter $C(V)$ is incremented after each assignment to $V$ is processed, so at most one assignment targets $V_i$. If $V_i$ is used, then $i$ was on top of $S(V)$ when the use was renamed, and $i$ was pushed when an assignment to $V$ was changed into an assignment to $V_i$.

## Depends on

- [Translation to static single assignment form](translation-to-static-single-assignment-form.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 5.2: Lemma 8 with its proof.
