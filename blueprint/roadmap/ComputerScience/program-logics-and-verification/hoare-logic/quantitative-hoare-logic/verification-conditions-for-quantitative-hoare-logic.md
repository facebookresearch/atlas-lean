# Verification conditions for quantitative Hoare logic

Work with the commands and states of the [timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md) and with $\vdash_2$ of [quantitative Hoare logic](quantitative-hoare-logic.md). Annotate every loop with a potential, written $\{I\}\ \mathtt{while}\ b\ \mathtt{do}\ C$, and let $\lfloor C \rfloor$ erase the annotations. Define the prepotential $\mathrm{pre}(C, Q)$ by $\mathrm{pre}(\mathtt{skip}, Q) = Q + 1$, $\mathrm{pre}(x := a, Q)(s) = Q(s[a/x]) + 1$, $\mathrm{pre}(C_1 ; C_2, Q) = \mathrm{pre}(C_1, \mathrm{pre}(C_2, Q))$, $\mathrm{pre}(\mathtt{if}\ b\ \mathtt{then}\ C_1\ \mathtt{else}\ C_2, Q)(s) = \mathrm{pre}(C_i, Q)(s) + 1$ with $C_i$ the branch $b$ selects in $s$, and $\mathrm{pre}(\{I\}\ \mathtt{while}\ b\ \mathtt{do}\ C, Q) = I + 1$. The verification condition $\mathrm{vc}(C, Q)$ is true for $\mathtt{skip}$ and assignments, is $\mathrm{vc}(C_1, Q) \wedge \mathrm{vc}(C_2, Q)$ for conditionals and $\mathrm{vc}(C_1, \mathrm{pre}(C_2, Q)) \wedge \mathrm{vc}(C_2, Q)$ for sequences, and for a loop is

$$\mathrm{pre}(C, I + 1) \le I + \uparrow b \ \wedge\ Q \le I + \uparrow \neg b \ \wedge\ \mathrm{vc}(C, I + 1).$$

**Theorem.** For every unannotated command $c$ and potentials $P,Q$,

$$
\vdash_2\{P\}\,c\,\{Q\}
\quad\Longleftrightarrow\quad
\exists C.\ \lfloor C\rfloor=c\ \wedge\ \mathrm{vc}(C,Q)\ \wedge\ \mathrm{pre}(C,Q)\le P,
$$

where the final inequality is pointwise.

The [verification conditions of annotated IMP commands](../../verification-condition-generation/vc.md) have the same shape, but for the natural-number IMP and with Boolean assertions. Here the loop annotations are potentials. Together with quantitative-Hoare soundness, these conditions bound the running time and guarantee termination from states with finite initial prepotential.

## Proof sketch

For $\Leftarrow$, induction on $C$ shows that $\mathrm{vc}(C, Q)$ implies $\vdash_2\{\mathrm{pre}(C, Q)\}\,\lfloor C\rfloor\,\{Q\}$, and consequence weakens the precondition to $P$. For $\Rightarrow$, induction on the derivation builds $C$. It uses two weakening properties: if $Q' \le Q$ pointwise, then $\mathrm{pre}(C,Q') \le \mathrm{pre}(C,Q)$, and $\mathrm{vc}(C,Q)$ implies $\mathrm{vc}(C,Q')$. Both directions use only the rules of $\vdash_2$, not the timed semantics.

## Depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)
- [Timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md)

## Proof depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 3.2, "Verification Condition Generator", Lemma 3 (soundness, by induction on the command) and Lemma 4 (completeness).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document (version of February 6, 2026), Section 5.5 (definitions `strip`, `pre`, `vc`), Section 5.5.1 (lemma `vc_sound`) and Section 5.5.2 (lemmas `pre_mono`, `vc_mono` and the completeness lemma `⊢₂ {P} c {Q} ⟹ ∃C. strip C = c ∧ vc C Q ∧ (∀s. pre C Q s ≤ P s)`).
