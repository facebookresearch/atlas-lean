# Lengths of proofs of finite consistency statements

A theory $T$ extending $S^1_2$ cannot prove "there is no $T$-proof of a contradiction of length $n$" in length below $n^{\varepsilon}$, but a finitely axiomatized sequential theory proves these statements in length polynomial in $n$: Gödel's second theorem has no direct finite analogue.

Let $\mathcal T$ be the class of consistent arithmetical theories that extend Buss's theory $S^1_2$ by a polynomial-time decidable set of axioms. For $T\in\mathcal T$, let $\mathrm{Con}_T(x)$ express that there is no $T$-proof of contradiction of length $x$, and let $\bar n$ be the binary numeral of $n$, so that $\mathrm{Con}_T(\bar n)$ has length $O(\log n)$.

**Theorem (Friedman; Pudlák).** For every $T\in\mathcal T$ there is $\varepsilon>0$ such that every $T$-proof of $\mathrm{Con}_T(\bar n)$ has length at least $n^{\varepsilon}$. Moreover, if $T$ is sequential and finitely axiomatized, then $\mathrm{Con}_T(\bar n)$ has $T$-proofs of length polynomial in $n$.

**Finite incompleteness conjectures.** Pudlák's Conjecture $\mathrm{CON}^N$ states that for every $S\in\mathcal T$ there is $T\in\mathcal T$ such that the lengths of $S$-proofs of $\mathrm{Con}_T(\bar n)$ are not bounded by any polynomial in $n$; by a result of Krajíček and Pudlák it is equivalent to the non-existence of a length-optimal propositional proof system. Its uniform version $\mathrm{CON}$, that $S$-proofs of $\mathrm{Con}_T(\bar n)$ cannot be constructed in time polynomial in $n$, is equivalent to the non-existence of a p-optimal propositional proof system.

## Expansion

The lower bound adapts Gödel's diagonal argument to the finite setting: a sentence $\delta_T(\bar n)$ saying "I have no $T$-proof of length at most $n$" is true and has no short proof, and it follows from $\mathrm{Con}_T(\bar n)$ by a short proof; the better the upper bounds on those auxiliary proofs, the stronger the lower bound (with Rosser's C-rule it improves to $\Omega(n/\log^2 n)$). The upper bound uses partial truth definitions: proofs of bounded length contain only formulas of bounded complexity, and a sequential theory can define truth for those formulas and verify that each axiom is true and each rule preserves truth. The intended analogue of Gödel's theorem is therefore not that a theory cannot prove its own finite consistency efficiently, but that no single theory proves the finite consistency of all theories efficiently.

## Depends on

- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](../bounded-arithmetic-correspondences/buss-theories-s2i-and-t2i.md)
- [Optimal and p-optimal propositional proof systems](optimal-and-p-optimal-proof-systems.md)

## Proof depends on

- [Arithmetization of syntax and the diagonal lemma](../../arithmetization-of-syntax-and-the-diagonal-lemma.md)

## Sources

- Pavel Pudlák, "Incompleteness in the finite domain", *Bulletin of Symbolic Logic* 23(4):405–441, 2017, doi:10.1017/bsl.2017.32, arXiv:1601.01487v2 (Section 2.1: Definition 1 of the class $\mathcal T$; Section 3.1: Question 1, Theorem 3.1 and Conjecture $\mathrm{CON}^N$; Section 5: the equivalence of $\mathrm{CON}^N$ with the non-existence of length-optimal proof systems; Section 6.1: Conjecture $\mathrm{CON}$ and its equivalence with the non-existence of p-optimal proof systems).
