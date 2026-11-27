# Frege proof systems

A Frege system is a textbook Hilbert-style propositional calculus: finitely many sound axiom schemes and inference rules over a complete set of connectives, implicationally complete. Proof size is the number of symbols, and any two Frege systems in the same language p-simulate each other.

Fix a language of propositional formulas built from variables over a complete set of connectives. A *Frege system* $F$ is a finite set of sound inference rules, each a tuple of $n>0$ formula schemes from which the last (the conclusion) is derived from the first $n-1$ (the premises); rules with no premises are *axiom schemes*. A *Frege derivation* of length $l$ from premises $\alpha_1,\dots,\alpha_h$ is a sequence of formulas $\beta_1,\dots,\beta_l$ in which each $\beta_i$ is one of the $\alpha_j$ or the conclusion of an instance of a rule whose premises occur among $\beta_1,\dots,\beta_{i-1}$; a *Frege proof* of $\beta$ is a derivation with no premises and last line $\beta$. A Frege system must be *implicationally complete*: whenever $(\alpha_1\wedge\dots\wedge\alpha_h)\to\beta$ is valid, there is a derivation of $\beta$ from $\alpha_1,\dots,\alpha_h$. The *size* of a proof is its number of symbols.

For definiteness one may take Buss's system $F$ with connectives $\neg,\wedge,\vee,\to$, thirteen axiom schemes and modus ponens as its only rule.

Facts recorded in the sources:

- Every Frege system is sound and complete, and it is a propositional proof system in the sense of Cook and Reckhow (the function sending a correct proof to its last line).
- Any two Frege systems in the same language p-simulate each other (Cook and Reckhow); Reckhow extended this to Frege systems in different languages under natural translations. So the choice of axioms, rules and connectives changes proof size by at most a polynomial.

## Expansion

Whether every tautology has polynomial-size Frege proofs is open; a positive answer would give $\mathsf{NP}=\mathsf{coNP}$, since the tautologies form a $\mathsf{coNP}$-complete set and having a polynomial-size Frege proof is an $\mathsf{NP}$ property. Under the correspondence between proof systems and circuit classes, the lines of Frege proofs are formulas, that is, $\mathsf{NC}^1$ circuits, so Frege is also called $\mathsf{NC}^1$-Frege. Restricting all formulas to depth at most a constant $d$ gives depth-$d$ (bounded-depth, $\mathsf{AC}^0$-) Frege, and adding the extension rule or the substitution rule gives extended Frege and substitution Frege.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Paola Bruscoli and Alessio Guglielmi, "On the proof complexity of deep inference", *ACM Transactions on Computational Logic* 10(2):14, 2009, doi:10.1145/1462179.1462186, arXiv:0709.1201v3 (Section 4: Definition 4.1 of Frege systems, derivations, implicational completeness and size; Theorem 4.2 (robustness, Cook and Reckhow) and the remark on Reckhow's generalization).
- Samuel R. Buss, "Polynomial size proofs of the propositional pigeonhole principle", *Journal of Symbolic Logic* 52(4):916–927, 1987, doi:10.2307/2273826 (Section 2: the Frege system $F$ with thirteen axioms and modus ponens, proof size, and the polynomial equivalence of any two Frege systems).
- Samuel R. Buss, "Bounded arithmetic and propositional proof complexity", in *Logic of Computation* (H. Schwichtenberg, ed.), Springer, 1997, author's copy <https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/paper.pdf> (Section 5.1: the definition of Frege systems, the open question of polynomial-size Frege proofs and its relation to $\mathsf{NP}=\mathsf{coNP}$, and Theorem 24 (Reckhow); Section 5.2: Frege systems as propositional proof systems, sending a valid proof to its last line; Section 6.3: depth of Frege proofs).
- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2.1: bounded-depth or $\mathsf{AC}^0$-Frege and $\mathsf{NC}^1$-Frege).
