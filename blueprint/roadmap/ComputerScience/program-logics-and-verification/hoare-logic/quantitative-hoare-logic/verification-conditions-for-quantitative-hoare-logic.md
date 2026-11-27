# Verification conditions for quantitative Hoare logic

Annotate every loop with a potential, written $\{I\}\ \mathtt{while}\ b\ \mathtt{do}\ C$, and let $\lfloor C \rfloor$ erase the annotations. Define the prepotential $\mathrm{pre}(C, Q)$ by $\mathrm{pre}(\mathtt{skip}, Q) = Q + 1$, $\mathrm{pre}(x := a, Q)(s) = Q(s[a/x]) + 1$, $\mathrm{pre}(C_1 ; C_2, Q) = \mathrm{pre}(C_1, \mathrm{pre}(C_2, Q))$, $\mathrm{pre}(\mathtt{if}\ b\ \mathtt{then}\ C_1\ \mathtt{else}\ C_2, Q)(s) = \mathrm{pre}(C_i, Q)(s) + 1$ with $C_i$ the branch $b$ selects in $s$, and $\mathrm{pre}(\{I\}\ \mathtt{while}\ b\ \mathtt{do}\ C, Q) = I + 1$. The verification condition $\mathrm{vc}(C, Q)$ is true for $\mathtt{skip}$ and assignments, is $\mathrm{vc}(C_1, Q) \wedge \mathrm{vc}(C_2, Q)$ for conditionals and $\mathrm{vc}(C_1, \mathrm{pre}(C_2, Q)) \wedge \mathrm{vc}(C_2, Q)$ for sequences, and for a loop is
$$\mathrm{pre}(C, I + 1) \le I + \uparrow b \ \wedge\ Q \le I + \uparrow \neg b \ \wedge\ \mathrm{vc}(C, I + 1).$$

**Theorem.** For every unannotated command $c$ and potentials $P,Q$,

$$
\vdash_2\{P\}\,c\,\{Q\}
\quad\Longleftrightarrow\quad
\exists C.\ \lfloor C\rfloor=c\ \wedge\ \mathrm{vc}(C,Q)\ \wedge\ \mathrm{pre}(C,Q)\le P,
$$

where the final inequality is pointwise.

Compared with the [verification conditions of annotated IMP commands](../../verification-condition-generation/vc.md), the loop annotations are potentials, so the same conditions also bound the running time and guarantee termination.

## Depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)

## Proof depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 3.2, "Verification Condition Generator", Lemma 3 (soundness, by induction on the command) and Lemma 4 (completeness).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document, Section 5.5 (definitions `strip`, `pre`, `vc` and lemma `vc_sound`).
