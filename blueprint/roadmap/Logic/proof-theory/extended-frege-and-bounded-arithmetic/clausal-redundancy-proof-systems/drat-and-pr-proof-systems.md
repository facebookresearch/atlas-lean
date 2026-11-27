# DRAT, PR and related clausal proof systems

The proof systems BC, RAT, SPR, PR and SR refute a clause set by repeatedly adding RUP clauses or clauses that satisfy the corresponding redundancy rule; their D-variants (DRAT, DPR, ...) also allow deletion, and their minus-variants (DRAT$^-$, PR$^-$, ...) forbid new variables.

Let $X$ be one of BC, RAT, SPR, PR, SR.

- An *$X$ proof* (refutation) of a clause set $\Gamma$ is a sequence $\Gamma_0,\dots,\Gamma_m$ with $\Gamma_0=\Gamma$, $\bot\in\Gamma_m$, and $\Gamma_{i+1}=\Gamma_i\cup\{C\}$ where either $\Gamma_i\vdash_1 C$ or $C$ is $X$ with respect to $\Gamma_i$. A BC or RAT step must specify its literal $p$, and an SPR, PR or SR step its witness $\tau$. The added clauses may contain variables that do not occur in $\Gamma_0,\dots,\Gamma_i$.
- A $DX$ proof (DBC, DRAT, DSPR, DPR, DSR) may in addition use the *deletion rule* $\Gamma_{i+1}=\Gamma_i\setminus\{C\}$ for any $C\in\Gamma_i$, including clauses of $\Gamma$. For $X=\mathrm{RAT}$ this is the system of [DRAT proofs](../../../propositional-logic/sat-solving/drat-proofs.md): additions of RUP or RAT clauses, arbitrary deletions, and an accumulated formula containing the empty clause, read with clauses non-tautological as in the RAT convention on [the redundancy page](propagation-and-substitution-redundancy.md).
- An $X$ or $DX$ refutation *without new variables*, written $X^-$ or $DX^-$ (for example BC$^-$, RAT$^-$, SPR$^-$, PR$^-$, DRAT$^-$, DPR$^-$), is one in which only variables of $\Gamma$ appear.

Facts recorded in the source:

- Every such system is sound, because each added clause preserves satisfiability, and it is polynomial-time verifiable because the witnesses are part of the proof; hence all of them are propositional proof systems in the sense of Cook and Reckhow.
- RUP steps simulate resolution steps, so all these systems p-simulate resolution.
- Deletion only removes clauses, so it can turn an unsatisfiable $\Gamma_i$ into a satisfiable $\Gamma_{i+1}$; this is harmless for refutations, and because the redundancy conditions quantify over the current clause set, deletion can make further inferences possible.
- The stricter reading of "no new variables", in which a variable eliminated by deletion may not be reused, changes refutation size by at most a polynomial.

## Expansion

DRAT, the case $DX$ with $X=\mathrm{RAT}$, is the clausal proof format used to certify unsatisfiability answers of SAT solvers: RUP steps cover resolution and conflict-driven clause learning, RAT steps cover inprocessing techniques such as blocked clause addition and the pure literal rule, and deletions keep checking efficient. Here "$P$ simulates $Q$" means that $Q$-proofs can be converted in polynomial time into $P$-proofs of the same clause set. With new variables, [extended resolution polynomially simulates DRAT](../../../propositional-logic/sat-solving/extended-resolution-simulates-drat.md).

## Depends on

- [Blocked, RAT, propagation-redundant and substitution-redundant clauses](propagation-and-substitution-redundancy.md)
- [DRAT proofs](../../../propositional-logic/sat-solving/drat-proofs.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Definitions 1.16 to 1.18 and the discussion in Sections 1.3 and 1.4; the meaning of "simulate" in Section 1).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: the DRAT proof system, RAT combined with clause deletion, used for proof logging).
