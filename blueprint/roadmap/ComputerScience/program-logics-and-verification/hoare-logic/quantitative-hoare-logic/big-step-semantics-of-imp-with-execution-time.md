# Timed big-step semantics of IMP with integer states

This page fixes the source's while language. Variables are strings, values are integers, and a state is a function $s$ from strings to $\mathbb{Z}$.

- *Arithmetic expressions* are integer constants $n$, variables $x$, and $a_1 + a_2$, $a_1 \cdot a_2$ and $a_1 \mathbin{\mathrm{div}} a_2$. The value $a(s)$ is $n$, $s(x)$, the sum, the product, or the integer quotient. Here $\mathrm{div}$ is the integer division of Isabelle/HOL, which rounds toward $-\infty$ and gives $0$ when the divisor is $0$.
- *Boolean expressions* are the constants true and false, $\neg b$, $b_1 \wedge b_2$ and $a_1 < a_2$, with the usual truth values in $s$.
- *Commands* are $\mathtt{skip}$, assignments $x := a$, sequences $c_1 ; c_2$, conditionals $\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ and loops $\mathtt{while}\ b\ \mathtt{do}\ c$.

The timed big-step relation $(c, s) \Rightarrow_p t$ says that running $c$ from $s$ terminates in $t$ after $p \in \mathbb{N}$ time units. It is the least relation closed under the following rules, which charge one unit for $\mathtt{skip}$, for an assignment and for each evaluation of a guard. Here $s[x \mapsto v]$ agrees with $s$ except that $x$ has value $v$.

- $(\mathtt{skip}, s) \Rightarrow_1 s$ and $(x := a, s) \Rightarrow_1 s[x \mapsto a(s)]$;
- if $(c_1, s) \Rightarrow_{p_1} u$ and $(c_2, u) \Rightarrow_{p_2} t$, then $(c_1 ; c_2, s) \Rightarrow_{p_1 + p_2} t$;
- if $b$ is true in $s$ and $(c_1, s) \Rightarrow_p t$, then $(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, s) \Rightarrow_{p + 1} t$, and likewise with $c_2$ when $b$ is false in $s$;
- if $b$ is false in $s$, then $(\mathtt{while}\ b\ \mathtt{do}\ c, s) \Rightarrow_1 s$;
- if $b$ is true in $s$, $(c, s) \Rightarrow_{p_1} u$ and $(\mathtt{while}\ b\ \mathtt{do}\ c, u) \Rightarrow_{p_2} t$, then $(\mathtt{while}\ b\ \mathtt{do}\ c, s) \Rightarrow_{1 + p_1 + p_2} t$.

This language is not the [IMP of the operational-semantics pages](../../../programming-language-semantics/operational-semantics-of-imp/state.md). That IMP has natural-number variables and values, subtraction but no division, and the comparisons $=$ and $\le$. No correspondence between the two languages is stated here. The cost model also differs from the [counted semantics of bounded symbolic execution](../../../programming-language-semantics/bounded-symbolic-execution-for-imp/big-step-cost.md), which counts only entries into loop bodies.

## Depends on

No separate prerequisite pages: the language, its states and the evaluation of its expressions are defined above.

## Proof depends on

Definition only; no proof prerequisites.

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 2 (the language IMP; skip, assignment and each evaluation of a Boolean expression cost one unit).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document (version of February 6, 2026), Section 1.1 (`vname = string`, `val = int`, `state = vname ⇒ val`, datatype `aexp` with `N`, `V`, `Plus`, `Times`, `Div`, and `aval`), Section 1.2 (datatype `bexp` with `Bc`, `Not`, `And`, `Less`, and `bval`), Section 2 (datatype `com`) and Section 3.1 (inductive definition `big_step_t`).
