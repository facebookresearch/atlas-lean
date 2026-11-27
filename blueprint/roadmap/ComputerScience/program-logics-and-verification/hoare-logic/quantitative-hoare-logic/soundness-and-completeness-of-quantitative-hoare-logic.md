# Soundness and completeness of quantitative Hoare logic

For every command $c$ and potentials $P$, $Q$ of [quantitative Hoare logic](quantitative-hoare-logic.md),

$$
\vdash_2 \{P\}\, c\, \{Q\}
\quad\Longleftrightarrow\quad
\models_2 \{P\}\, c\, \{Q\}.
$$

Potentials are arbitrary functions on states, so completeness needs no expressiveness hypothesis.

## Proof sketch

Induction on the timed semantics shows that its terminating runs are exactly the [big-step runs of IMP](../../../programming-language-semantics/operational-semantics-of-imp/big-step.md), with a unique time and final state. Write those as $\downarrow_T(c,s)$ and $\downarrow_S(c,s)$.

Soundness follows by induction on the Hoare derivation; the loop case additionally uses induction on the finite value of the invariant potential. For completeness, define $\mathrm{wp}(c,Q)(s)$ to be $\downarrow_T(c,s)+Q(\downarrow_S(c,s))$ on a terminating run and $\infty$ otherwise. The source's weakest-prepotential lemma derives $\vdash_2\{\mathrm{wp}(c,Q)\}\,c\,\{Q\}$. Validity is equivalent to $\mathrm{wp}(c,Q)\le P$ pointwise, so consequence gives the required derivation.

## Depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)
- [Big-step semantics of IMP with execution time](big-step-semantics-of-imp-with-execution-time.md)

## Proof depends on

- [Big-step semantics of IMP](../../../programming-language-semantics/operational-semantics-of-imp/big-step.md)
- [Big-step semantics of IMP with execution time](big-step-semantics-of-imp-with-execution-time.md)
- [Determinism of IMP big-step semantics](../../../programming-language-semantics/operational-semantics-of-imp/deterministic.md)

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 3.2, Theorem 5 (soundness), the weakest prepotential, Lemma 2 and Theorem 6 (completeness).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document, Section 3.3 (relation to the big-step semantics), Section 3.4 (theorem `big_step_t_determ2`), Sections 5.3 and 5.4 (theorems `hoare2_sound`, `wp2_is_weakestprePotential`, `wp2_is_pre`, `hoare2_complete`).
