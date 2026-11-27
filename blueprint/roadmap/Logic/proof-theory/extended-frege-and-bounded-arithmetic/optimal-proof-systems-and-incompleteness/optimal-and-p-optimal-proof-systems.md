# Optimal and p-optimal propositional proof systems

A propositional proof system is optimal if it simulates every propositional proof system, up to a polynomial increase in proof length, and p-optimal if it p-simulates every propositional proof system. Whether such systems exist is a central open problem.

Let $P$ and $Q$ be propositional proof systems, that is, polynomial-time functions onto the set $\mathrm{TAUT}$ of tautologies. Write $Q\le P$ ($P$ *simulates* $Q$) if there is a polynomial $p$ such that every tautology with a $Q$-proof $\pi$ has a $P$-proof of size at most $p(|\pi|)$, and $Q\le_p P$ ($P$ *p-simulates* $Q$) if moreover such $P$-proofs are computable from $\pi$ in polynomial time.

- $P$ is *optimal* (Pudlák: *length-optimal*) if $Q\le P$ for every propositional proof system $Q$.
- $P$ is *p-optimal* if $Q\le_p P$ for every propositional proof system $Q$.
- $P$ is *polynomially bounded* if there is a polynomial $p$ such that every tautology $\varphi$ has a $P$-proof of size at most $p(|\varphi|)$.

Every p-optimal system is optimal, and a polynomially bounded system is optimal. A sequence of tautologies $(\varphi_n)$ is *hard* for $P$ if it is constructible in polynomial time from $1^n$ and has no $P$-proofs of size polynomial in $|\varphi_n|$.

## Expansion

A polynomially bounded system exists iff $\mathsf{NP}=\mathsf{coNP}$ ([Cook–Reckhow theorem](../../../propositional-logic/propositional-proof-complexity/cookreckhow-theorem.md)), so optimality is the weaker, "relative" version of the question that motivated proof complexity: if no optimal system exists, then no sequence of ever stronger systems can be capped by a single best one. Pudlák conjectures that no length-optimal system exists (Conjecture $\mathrm{CON}^N$) and that no p-optimal system exists (Conjecture $\mathrm{CON}$); these conjectures are equivalent to finite versions of Gödel's second incompleteness theorem about proofs of bounded consistency statements. Krajíček showed that the p-optimality of a system is equivalent to the existence of a time-optimal proof search algorithm. A length-optimal system would make its canonical disjoint NP pair complete for disjoint NP pairs.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 3: simulation $\le$, p-simulation $\le_p$, and optimal proof systems; Section 12: hard sequences of tautologies; pre-review numbering).
- Pavel Pudlák, "Incompleteness in the finite domain", *Bulletin of Symbolic Logic* 23(4):405–441, 2017, doi:10.1017/bsl.2017.32, arXiv:1601.01487v2 (Section 5: polynomially bounded and length-optimal proof systems, Conjecture $\mathrm{CON}^N$ and Proposition 5.2; Section 6.1: Definition 9 (polynomial simulation and p-optimality) and Conjecture $\mathrm{CON}$).
- Jan Krajíček, "A proof complexity conjecture and the incompleteness theorem", *Journal of Symbolic Logic* 90(3):1206–1210, 2025 (published online 2023), doi:10.1017/jsl.2023.69, arXiv:2303.10637v2 (Section 3: the non-existence of a p-optimal system is equivalent to the non-existence of a time-optimal propositional proof search algorithm).
- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001, <https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2014W/BeamePitassi_pastpresentfuture.pdf> (Section 3.7: the open question whether an optimal proof system exists).
