# Quantitative Hoare logic

Commands, expressions and states are those of the [timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md): states map strings to integers. A *potential* is a function $P$ from these states to $\mathbb{N} \cup \{\infty\}$; potentials are added and compared pointwise, and $P + 1$ is $s \mapsto P(s) + 1$. A predicate $B$ on states lifts to the potential $\uparrow B$ with $\uparrow B(s) = 0$ if $B(s)$ holds and $\infty$ otherwise; for a guard $b$, $\uparrow b(s) = 0$ if $b$ is true in $s$ and $\infty$ otherwise.

**Validity.** A quantitative triple $\{P\}\, c\, \{Q\}$ is *valid*, written $\models_2 \{P\}\, c\, \{Q\}$, if for every state $s$ with $P(s) < \infty$ there are a state $t$ and a time $p$ with $(c, s) \Rightarrow_p t$ in the timed semantics and $p + Q(t) \le P(s)$. A finite prepotential thus guarantees termination, and the difference between pre- and postpotential bounds the running time.

**Rules.** Derivability $\vdash_2 \{P\}\, c\, \{Q\}$ is the least relation closed under the following rules, where $s[a/x]$ is $s$ with $x$ set to the value of $a$ in $s$:

- **Skip.** $\vdash_2 \{P + 1\}\ \mathtt{skip}\ \{P\}$.
- **Assign.** $\vdash_2 \{s \mapsto P(s[a/x]) + 1\}\ x := a\ \{P\}$.
- **If.** From $\vdash_2 \{P + \uparrow b\}\, c_1\, \{Q\}$ and $\vdash_2 \{P + \uparrow \neg b\}\, c_2\, \{Q\}$ infer $\vdash_2 \{P + 1\}\ \mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\ \{Q\}$.
- **Seq.** From $\vdash_2 \{P_1\}\, c_1\, \{P_2\}$ and $\vdash_2 \{P_2\}\, c_2\, \{P_3\}$ infer $\vdash_2 \{P_1\}\, c_1 ; c_2\, \{P_3\}$.
- **While.** From $\vdash_2 \{I + \uparrow b\}\, c\, \{I + 1\}$ infer $\vdash_2 \{I + 1\}\ \mathtt{while}\ b\ \mathtt{do}\ c\ \{I + \uparrow \neg b\}$.
- **Consequence.** From $\vdash_2 \{P\}\, c\, \{Q\}$, $P \le P'$ and $Q' \le Q$ pointwise, infer $\vdash_2 \{P'\}\, c\, \{Q'\}$.

The added $1$ pays for $\mathtt{skip}$, for an assignment and for each evaluation of a guard; the loop rule needs no separate variant, since the invariant potential decreases with every iteration. Potentials in assertions are the program-logic form of the [potential method of amortized analysis](../../../data-structures/amortized-analysis/README.md); [Nielson's calculus](../../expected-run-time-calculus/nielsons-calculus-for-run-time-bounds.md) is a related logic for orders of magnitude.

## Depends on

- [Timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md)

## Proof depends on

Definition only; no proof prerequisites.

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 3.2 and Fig. 3 (potentials, the lifting $\uparrow$, validity of quantitative triples and the rules of $\vdash_2$).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document (version of February 6, 2026), Sections 5.1 and 5.2 (definitions `hoare2_valid`, `emb` and the inductive definition `hoare2`, over the states of Section 1.1).
