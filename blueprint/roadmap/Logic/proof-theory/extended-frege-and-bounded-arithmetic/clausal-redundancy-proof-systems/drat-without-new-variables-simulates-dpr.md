# DRAT without new variables simulates DPR without new variables

Even without new variables, deletion-based propagation redundancy collapses: DRAT$^-$ p-simulates DPR$^-$, so DBC$^-$, DRAT$^-$, DSPR$^-$ and DPR$^-$ are all polynomially equivalent.

**Theorem (Buss–Thapen).** DRAT$^-$ simulates DPR$^-$: every DPR refutation of a clause set $\Gamma$ that uses only variables of $\Gamma$ can be converted in polynomial time into a DRAT refutation of $\Gamma$ that uses only variables of $\Gamma$.

Together with the simulation of DRAT$^-$ by DBC$^-$ (Kiesl, Rebola-Pardo and Heule) and the trivial inclusions, the systems DBC$^-$, DRAT$^-$, DSPR$^-$ and DPR$^-$ are equivalent.

## Expansion

Heule and Biere showed that a PR inference can be replaced by a polynomial-size DRAT derivation that uses one new variable $x$: RAT steps on $x$ add copies of the clauses of $\Gamma|_\tau$ and of $C$ guarded by a literal of $x$, RAT steps on the literals of $\tau$ then link $x$ to $\tau$, resolution recovers $C$ and the temporarily weakened clauses, and the auxiliary clauses are deleted (Lemma 3.4). To avoid the new variable, Buss and Thapen eliminate a variable $x$ of $\Gamma$ by passing to $\Gamma^{(x)}$, the clauses not mentioning $x$ together with all resolvents on $x$; $\Gamma$ is recovered from $\Gamma^{(x)}$ by a polynomial-size DRAT derivation without new variables (Lemma 3.6). Every PR inference is first normalized to a $\mathrm{PR}_0$ inference (Lemma 3.7), which remains $\mathrm{PR}_0$ after eliminating a variable outside the domain of its witness (Lemma 3.8); the freed variable then plays the role of $x$.

## Depends on

- [DRAT, PR and related clausal proof systems](drat-and-pr-proof-systems.md)

## Proof depends on

- [Blocked, RAT, propagation-redundant and substitution-redundant clauses](propagation-and-substitution-redundancy.md)

## Sources

- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Section 3.1: Theorems 3.1 and 3.2 (prior results), Theorem 3.3, Lemma 3.4, Definition 3.5, Lemmas 3.6 to 3.8).
