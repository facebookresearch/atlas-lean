# Exponential lower bound for DRAT without new variables on the bit pigeonhole principle

DRAT refutations of the bit pigeonhole principle that use no new variables and never delete its axioms need size at least $2^{n/60}$. Hence RAT$^-$ does not simulate DRAT$^-$ or SPR$^-$: without new variables, deletion adds exponential power.

**Theorem (Buss–Thapen).** Let $n=2^k$ and let $\Pi$ be a DRAT$^-$ refutation of $\mathrm{BPHP}_n$ in which no clause of $\mathrm{BPHP}_n$ is ever deleted. Then $\Pi$ has size at least $2^{n/60}$.

**Corollary.** RAT$^-$ does not simulate DRAT$^-$, and RAT$^-$ does not simulate SPR$^-$.

Here the *pigeon-width* of a clause is the number of distinct pigeons whose variables it mentions.

## Expansion

The key step is a width bound: if $\rho$ is a partial matching of at most $n/4$ pigeons to holes and $\Pi$ is a DRAT$^-$ refutation of $\mathrm{BPHP}_n\cup\rho$ that never deletes axioms, then some clause of $\Pi$ has pigeon-width more than $n/3$ (Theorem 5.3, proved through a Prover–Adversary game, Lemmas 5.1 and 5.2). For the size bound, choose a random restriction that selects each pigeon with probability $1/5$ and matches the selected pigeons to random distinct holes; a clause of pigeon-width at least $n/4$ survives with probability at most $e^{-n/60}$, so if $\Pi$ had at most $2^{n/60}$ wide clauses some restriction would kill all of them while setting at most $n/4$ pigeons, contradicting the width bound. For the corollary, $\mathrm{BPHP}_n$ has polynomial-size SPR$^-$ refutations and hence DRAT$^-$ refutations, while RAT$^-$ has no deletion at all.

## Depends on

- [DRAT, PR and related clausal proof systems](drat-and-pr-proof-systems.md)

## Proof depends on

- [SPR refutations of pigeonhole principles without new variables](spr-without-new-variables-refutes-pigeonhole.md)
- [DRAT without new variables simulates DPR without new variables](drat-without-new-variables-simulates-dpr.md)

## Sources

- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Section 5: Lemmas 5.1 and 5.2, Theorem 5.3, Theorem 5.4 and Corollary 5.5; Section 4.2 for $\mathrm{BPHP}_n$).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: without new variables there is an exponential separation between RAT and DRAT).
