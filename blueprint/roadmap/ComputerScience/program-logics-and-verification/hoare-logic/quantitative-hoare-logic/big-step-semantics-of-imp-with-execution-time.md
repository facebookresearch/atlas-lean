# Big-step semantics of IMP with execution time

For the deterministic while language with $\mathtt{skip}$, assignment, sequencing, conditionals and while loops, whose states map variables to values, the timed big-step relation $(c, s) \Rightarrow_p t$ says that running $c$ from $s$ terminates in $t$ after $p \in \mathbb{N}$ time units. It is the least relation closed under the following rules, which charge one unit for $\mathtt{skip}$, for an assignment and for each evaluation of a guard:

- $(\mathtt{skip}, s) \Rightarrow_1 s$ and $(x := a, s) \Rightarrow_1 s[x \mapsto a(s)]$;
- if $(c_1, s) \Rightarrow_{p_1} u$ and $(c_2, u) \Rightarrow_{p_2} t$, then $(c_1 ; c_2, s) \Rightarrow_{p_1 + p_2} t$;
- if $b$ is true in $s$ and $(c_1, s) \Rightarrow_p t$, then $(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, s) \Rightarrow_{p + 1} t$, and likewise with $c_2$ when $b$ is false in $s$;
- if $b$ is false in $s$, then $(\mathtt{while}\ b\ \mathtt{do}\ c, s) \Rightarrow_1 s$;
- if $b$ is true in $s$, $(c, s) \Rightarrow_{p_1} u$ and $(\mathtt{while}\ b\ \mathtt{do}\ c, u) \Rightarrow_{p_2} t$, then $(\mathtt{while}\ b\ \mathtt{do}\ c, s) \Rightarrow_{1 + p_1 + p_2} t$.

This cost model differs from the [counted semantics of bounded symbolic execution](../../../programming-language-semantics/bounded-symbolic-execution-for-imp/big-step-cost.md), which counts only entries into loop bodies.

## Depends on

- [Big-step semantics of IMP](../../../programming-language-semantics/operational-semantics-of-imp/big-step.md)

## Proof depends on

Definition only; no proof prerequisites.

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 2 (skip, assignment and each evaluation of a Boolean expression cost one unit).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document, Section 3.1 (inductive definition `big_step_t`). The source's states map string variable names to integers.
