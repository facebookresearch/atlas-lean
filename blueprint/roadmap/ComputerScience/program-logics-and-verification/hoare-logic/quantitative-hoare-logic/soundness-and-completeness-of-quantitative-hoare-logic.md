# Soundness and completeness of quantitative Hoare logic

For every command $c$ of the [timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md) and potentials $P$, $Q$ on its states, with $\vdash_2$ and $\models_2$ as in [quantitative Hoare logic](quantitative-hoare-logic.md),

$$
\vdash_2 \{P\}\, c\, \{Q\}
\quad\Longleftrightarrow\quad
\models_2 \{P\}\, c\, \{Q\}.
$$

Potentials are arbitrary functions on states, so completeness needs no expressiveness hypothesis.

## Expansion

The completeness direction needs determinism of the timed semantics on this page's language: if $(c, s) \Rightarrow_p t$ and $(c, s) \Rightarrow_q u$, then $p = q$ and $t = u$. That is what makes the weakest prepotential below well defined, and the equivalence of validity with $\mathrm{wp}(c, Q) \le P$ uses it too. The source proves it as `big_step_t_determ2`, by induction on the timed relation. No page states it yet. The repository's [determinism of IMP big-step semantics](../../../programming-language-semantics/operational-semantics-of-imp/deterministic.md) concerns the natural-number IMP, an untimed relation, and a different expression language, so it does not supply it. No transfer between the two languages is claimed. Before this page becomes ready, add a page for timed determinism, sourced from the theory document's Section 3.4, and list it under Proof depends on.

## Proof sketch

Assuming that determinism, a terminating run of $c$ from $s$ has a unique time $\downarrow_T(c,s)$ and a unique final state $\downarrow_S(c,s)$.

Soundness follows by induction on the Hoare derivation; the loop case additionally uses induction on the finite value of the invariant potential. For completeness, define $\mathrm{wp}(c,Q)(s)$ to be $\downarrow_T(c,s)+Q(\downarrow_S(c,s))$ on a terminating run and $\infty$ otherwise. The source's weakest-prepotential lemma derives $\vdash_2\{\mathrm{wp}(c,Q)\}\,c\,\{Q\}$. Validity is equivalent to $\mathrm{wp}(c,Q)\le P$ pointwise, so consequence gives the required derivation.

## Depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)
- [Timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md)

## Proof depends on

- [Quantitative Hoare logic](quantitative-hoare-logic.md)
- [Timed big-step semantics of IMP with integer states](big-step-semantics-of-imp-with-execution-time.md)

Determinism of the timed semantics is also required; see Expansion.

## Sources

- M. P. L. Haslbeck and T. Nipkow, "Hoare logics for time bounds: a study in meta theory", *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2018)*, LNCS 10805, Springer, 2018, pp. 155–171, open access, <https://doi.org/10.1007/978-3-319-89960-2_9>, Section 3.2, Theorem 5 (soundness), the weakest prepotential, Lemma 2 and Theorem 6 (completeness).
- M. P. L. Haslbeck and T. Nipkow, "Hoare Logics for Time Bounds", *Archive of Formal Proofs*, 2018, <https://www.isa-afp.org/entries/Hoare_Time.html>, theory document (version of February 6, 2026), Section 3.4 (theorem `big_step_t_determ2` and the abbreviations `↓`, `↓s`, `↓t`), Sections 5.3 and 5.4 (theorems `hoare2_sound`, `wp2_is_weakestprePotential`, `wp2_is_pre`, `hoare2_complete`).
