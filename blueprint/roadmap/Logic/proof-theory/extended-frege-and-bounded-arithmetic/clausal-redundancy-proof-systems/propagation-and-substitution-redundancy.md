# Blocked, RAT, propagation-redundant and substitution-redundant clauses

Clause-redundancy rules let a refutation add a clause $C$ to a clause set $\Gamma$ without loss of generality: blocked clauses, RAT clauses, subset propagation redundant (SPR), propagation redundant (PR) and substitution redundant (SR) clauses, in increasing order of strength, all keep $\Gamma$ and $\Gamma\cup\{C\}$ equisatisfiable.

A clause is a non-tautological set of literals; for a clause $C$, $\alpha=\overline{C}$ is the partial assignment with domain the variables of $C$ that falsifies $C$. A substitution $\sigma$ maps variables to literals or constants; it *satisfies* $C$, written $\sigma\vDash C$, if $1\in\sigma(C)$ or $\sigma(C)$ is tautological, and otherwise $C|_\sigma=\sigma(C)\setminus\{0\}$. For a clause set, $\Gamma|_\sigma=\{C|_\sigma : C\in\Gamma,\ \sigma\nvDash C\}$. Write $\Gamma\vdash_1\bot$ if unit propagation refutes $\Gamma$, $\Gamma\vdash_1 C$ if $\Gamma\cup\overline{C}\vdash_1\bot$, and $\Gamma\vdash_1\Delta$ if $\Gamma\vdash_1 D$ for all $D\in\Delta$. Thus $\Gamma\vdash_1 C$ says that $C$ is a RUP clause (asymmetric tautology) with respect to $\Gamma$, and *RAT clauses* are as defined on [RUP and RAT clauses](../../../propositional-logic/proof-certificates/rup-and-rat-clauses.md). That page allows tautological clauses, and Buss and Thapen do not: in their Definition 1.7 a resolvent $C'\cup D'$ on $p$ that is tautological is exempted explicitly, while on that page it is an asymmetric tautology automatically, and the remaining check $\Gamma\vdash_1 p\vee C'\vee D'$ is the LRAT form recorded there. So the two definitions of RAT agree on non-tautological clauses.

Let $C=p\vee C'$ with distinguished literal $p$.

- $C$ is a *blocked clause* (BC) with respect to $p$ and $\Gamma$ if for every clause $\bar p\vee D'$ in $\Gamma$ the set $C'\cup D'$ is tautological.
- $C$ is *subset propagation redundant* (SPR) with respect to $\Gamma$ if there is a partial assignment $\tau$ with $\mathrm{dom}(\tau)=\mathrm{dom}(\alpha)$, $\tau\vDash C$ and $\Gamma|_\alpha\vdash_1\Gamma|_\tau$.
- $C$ is *propagation redundant* (PR) with respect to $\Gamma$ if there is a partial assignment $\tau$ with $\tau\vDash C$ and $\Gamma|_\alpha\vdash_1\Gamma|_\tau$.
- $C$ is *substitution redundant* (SR) with respect to $\Gamma$ if there is a substitution $\tau$ with $\tau\vDash C$ and $\Gamma|_\alpha\vdash_1\Gamma|_\tau$.

Basic facts proved in the source:

- $C$ is RAT with respect to $p$ and $\Gamma$ iff $\Gamma|_\alpha\vdash_1\Gamma|_\tau$ where $\tau$ agrees with $\alpha$ except that $\tau(p)=1$; so BC implies RAT implies SPR implies PR implies SR.
- If $C$ is SR (hence if it is BC, RAT, SPR or PR) with respect to $\Gamma$, then $\Gamma$ and $\Gamma\cup\{C\}$ are equisatisfiable.
- Given the witness $p$ or $\tau$, each condition is decidable in polynomial time.

## Expansion

For equisatisfiability, take a total assignment $\pi$ satisfying $\Gamma$. If $\pi\vDash C$ nothing is needed. Otherwise $\pi$ extends $\alpha$, so $\pi$ satisfies $\Gamma|_\alpha$ and therefore $\Gamma|_\tau$; then $\pi\circ\tau$ satisfies $\Gamma$ and also $C$, because $\tau\vDash C$. The rules do not respect implication (a RAT clause need not follow from $\Gamma$), and they are non-monotone: adding clauses to $\Gamma$ can invalidate an inference, while deleting clauses can enable new ones. RUP and RAT clauses are the clause notions checked by DRAT and LRAT proof checkers.

## Depends on

- [RUP and RAT clauses](../../../propositional-logic/proof-certificates/rup-and-rat-clauses.md)

## Proof depends on

None.

## Sources

- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Section 1.1: substitutions, restrictions and Lemma 1.1; Definition 1.2 of $\vdash_1$; Definitions 1.6 and 1.7 (BC, RAT); Theorem 1.10; Definitions 1.11 to 1.13 (SPR, PR, SR); Theorem 1.15 (equisatisfiability)).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: RAT inferences, which preserve satisfiability but not implication).
