# Hard tautologies exist exactly for non-optimal proof systems

For a proof system at least as strong as extended Frege and closed under substitutions and modus ponens, having a hard sequence of tautologies, being non-optimal, and failing to prove some reflection principle efficiently are equivalent (Krajíček).

**Theorem.** Let $P$ be a propositional proof system with $EF\le P$ that is closed under substitutions and modus ponens. The following are equivalent:

1. there is a sequence of tautologies hard for $P$;
2. $P$ is not optimal;
3. there is a propositional proof system $Q$ such that the tautologies $\lVert\mathrm{RFN}(Q)\rVert_n$ do not have $P$-proofs of size polynomial in $n$.

Here a sequence $(\varphi_n)$ is hard for $P$ if it is polynomial-time constructible from $1^n$ and has no polynomial-size $P$-proofs. $P$ is *closed under modus ponens* if there is a polynomial $p$ such that $P$-proofs of size at most $n$ of $\varphi_1,\dots,\varphi_k$ and of $\varphi_1\to\varphi_2\to\cdots\to\varphi_{k+1}$ imply a $P$-proof of $\varphi_{k+1}$ of size at most $p(n)$, and *closed under substitutions* if there is a polynomial $q$ such that a $P$-proof of $\varphi$ of size at most $n$ implies a $P$-proof of size at most $q(n+|\sigma(\varphi)|)$ of every substitution instance $\sigma(\varphi)$.

## Expansion

(1) implies (2): if $(\varphi_n)$ is hard for $P$, the system $Q=EF+\{\varphi_n : n\ge 0\}$ proves each $\varphi_n$ in polynomial size, so $P$ does not simulate $Q$. (2) implies (3): if $Q\not\le P$ but $P$ had polynomial-size proofs of $\lVert\mathrm{RFN}(Q)\rVert_n$, then, because $P\ge EF$ is closed under substitutions and modus ponens, $P$ would simulate $EF+\lVert\mathrm{RFN}(Q)\rVert$, which simulates $Q$; a contradiction. (3) implies (1) because $\lVert\mathrm{RFN}(Q)\rVert_n$ is itself polynomial-time constructible. Thus reflection principles of stronger systems are universal candidates for hard tautologies, though they resist combinatorial analysis.

## Depends on

- [Optimal and p-optimal propositional proof systems](optimal-and-p-optimal-proof-systems.md)
- [Reflection principle of a propositional proof system](reflection-principle-of-a-proof-system.md)
- [Extended Frege proof systems](../extended-and-substitution-frege/extended-frege-system.md)

## Proof depends on

- [Extended Frege is the proof system of $S^1_2$](../bounded-arithmetic-correspondences/extended-frege-corresponds-to-s21.md)

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 4: Definitions 4.1 and 4.2 of closure under modus ponens and under substitutions; Section 12: Theorem 12.1, attributed to Krajíček, with its proof via Lemma 11.4 and Proposition 11.7; definition of hard sequences; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
