# Auxiliary variables are needed for shared-variable parallelism

Without the auxiliary-variable rule the Owicki–Gries system is incomplete, and Olderog's adaptation rule does not repair it: the valid triple $\{\mathrm{true}\}\,[x := x + 2 \parallel x := 0]\,\{x = 0 \vee x = 2\}$ cannot be derived from Hoare's rules, the atomic-region rule and the parallel rule, even with Olderog's adaptation rule.

Use the rules of the [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md) over a first-order assertion language and interpretation, which the source leaves unspecified: the sequential rules $\mathrm{PW}$ (skip, assignment, sequencing, conditional, loop and consequence), the atomic-region rule AT, from $\{p\}\,S\,\{q\}$ infer $\{p\}\,\langle S \rangle\,\{q\}$, and the parallel rule PSV, from non-interfering proofs of $\{p_i\}\,S_i\,\{q_i\}$ infer $\{\bigwedge_i p_i\}\,[S_1 \parallel \dots \parallel S_n]\,\{\bigwedge_i q_i\}$, where a proof of $\{p\}\,S\,\{q\}$ does not interfere with one of $\{p'\}\,S'\,\{q'\}$ if $\{\mathrm{pre}(T) \wedge r\}\,T\,\{r\}$ is valid for every assertion $r$ of the second proof outside atomic regions and every substatement $T$ of $S$ outside atomic regions with its precondition $\mathrm{pre}(T)$ in the first proof. Olderog's adaptation rule OLD is: from $\{p\}\,S\,\{q\}$ and the validity of

$$p' \to \forall \bar y\,\big(\forall \bar z\,(p \to q[\bar x := \bar y]) \to q'[\bar x := \bar y]\big)$$

infer $\{p'\}\,S\,\{q'\}$, where $\bar x$ lists the program variables of $S$, $\bar y$ is a list of fresh variables of the same length, and $\bar z$ lists the free variables of $p$ and $q$ not in $\bar x$.

**Theorem.** The triple $\{\mathrm{true}\}\,[x := x + 2 \parallel x := 0]\,\{x = 0 \vee x = 2\}$ is valid but not derivable in $\mathrm{PW}$ + AT + PSV + OLD.

It is derivable once the auxiliary-variable rule is added, as Apt, de Boer and Olderog show. The rule OLD derives the invariance, substitution and $\exists$-introduction rules and the rule of consequence, so no combination of these replaces auxiliary variables here.

## Depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Proof depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Expansion

Validity holds because each assignment is atomic: running $x := x + 2$ first leaves $x = 0$, and running it second leaves $x = 2$. The source's proof of underivability uses two facts about OLD (the other adaptation rules are derivable from it, and consecutive OLD steps merge into one), so a derivation may be assumed to end with PSV on proofs of $\{p_1\}\,x := x + 2\,\{q_1\}$ and $\{p_2\}\,x := 0\,\{q_2\}$ followed by one OLD step; instantiating that step's premise at $x = 2$, $y = 4$ and using local correctness and two of the interference-freedom conditions yields a contradiction. A development needs those two facts about OLD. The source leaves open whether OLD is adaptation complete for parallel programs.

## Sources

- S. de Gouw and J. Rot, "Effectively eliminating auxiliaries", in *Theory and Practice of Formal Methods: Essays Dedicated to Frank de Boer on the Occasion of His 60th Birthday*, LNCS 9660, Springer, 2016, pp. 226–241, <https://doi.org/10.1007/978-3-319-30734-3_16>, author copy <http://jurriaan.creativecode.org/wp-content/uploads/2013/04/ghost.pdf>: Section 2.2 (Figure 1, Rule OLD, Lemma 1, Lemma 2, Lemma 3), Section 3 (Figure 3, proof system PW), Section 6 (Rule AT, Definition 5, Rule PSV, Theorem 5 and its proof, Remarks 2 and 3) and Table 1. Numbering follows the author copy.
- K. R. Apt and E.-R. Olderog, "Fifty years of Hoare's logic", *Formal Aspects of Computing* 31(6):751–807, 2019, <https://doi.org/10.1007/s00165-019-00501-3>, author version arXiv:1904.03917v1, <https://arxiv.org/abs/1904.03917v1>: Section 8.1 (auxiliary variables are essential for parallel programs with shared variables, following de Gouw and Rot).
- E.-R. Olderog, "On the notion of expressiveness and the rule of adaptation", *Theoretical Computer Science* 24(3):337–347, 1983, <https://doi.org/10.1016/0304-3975(83)90009-9>: not consulted; rule OLD and its adaptation completeness for finitely based state transformers are quoted from de Gouw and Rot, Section 2.2.
