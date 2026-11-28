# Extended Frege proof systems

An extended Frege system is a Frege system augmented with Tseitin's extension rule, which lets a proof introduce a fresh propositional variable as an abbreviation for an arbitrary formula. Proof size is the total number of symbols in the proof.

Fix a [Frege system](frege-system.md) $F$; for definiteness take Buss's system with connectives $\neg,\wedge,\vee,\to$, thirteen axiom schemes and modus ponens as its only rule. A sequence of formulas $A_1,\dots,A_k$ is an *extended Frege* ($eF$) *proof* of $A_k$ if every $A_i$ is an instance of an axiom scheme, follows from earlier lines by modus ponens, or is obtained by the *extension rule*, which allows

$$
A_i \;=\; (p \to B) \wedge (B \to p)
$$

whenever the propositional variable $p$ does not occur in $A_1,\dots,A_{i-1}$, in $A_k$, or in $B$. The size of a proof is its number of symbols, with variables written as the letter $p$ followed by decimal digits.

Equivalently, in the sequent calculus formulation, an extended Frege proof may use as extra initial sequents the extension axioms $x_i \Rightarrow \psi_i$ and $\psi_i \Rightarrow x_i$ for a sequence of pairs $(x_i,\psi_i)$, $i=1,\dots,k$, in which the extension variables $x_1,\dots,x_k$ are pairwise distinct and each $x_i$ does not occur in the conclusion of the proof nor in any $\psi_j$ with $j \le i$.

Facts recorded in the sources:

- Any two extended Frege systems p-simulate each other, so the choice of axioms, rules and connectives changes proof size by at most a polynomial.
- If a formula $\varphi$ has a Frege proof with $m$ inference steps, then $\varphi$ has an $eF$-proof of size $O(m+|\varphi|^2)$ (Statman); so the size of $eF$-proofs is essentially the number of lines of Frege proofs.
- Every extended Frege system is a propositional proof system in the sense of Cook and Reckhow; it is open whether Frege systems p-simulate extended Frege systems.

## Expansion

An extension line $p \leftrightarrow B$ is sound because $p$ is new: any truth assignment for the remaining variables extends uniquely to $p$ so that the line is true, and since $p$ does not occur in the conclusion, a proof whose lines are all true under every such extension proves a tautology. Expanding each extension variable into the formula it abbreviates turns an $eF$-proof into a Frege proof, but the formulas can grow exponentially because abbreviations nest. Through the extension rule a proof can reason about Boolean circuits rather than formulas, which is why extended Frege is often called $\mathsf{P/poly}$-Frege.

## Depends on

- [Frege proof systems](frege-system.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Samuel R. Buss, "Polynomial size proofs of the propositional pigeonhole principle", *Journal of Symbolic Logic* 52(4):916–927, 1987, doi:10.2307/2273826 (Section 2: the Frege system $F$, the extended Frege system $eF$, the extension rule, symbol size, and the open problem whether $F$ p-simulates $eF$).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.9: the extension axioms (7.75) for the sequent calculus formulation, with each $x_i$ a new variable).
- Sam Buss, "Proof Complexity, Part A: Introduction, Frege proofs, abstract proof systems and resolution", lecture slides, Satisfiability Boot Camp, Simons Institute, 2021, <https://mathweb.ucsd.edu/~sbuss/ResearchWeb/Simons_BootCamp_2021/talkslidesA.pdf> (slide headed "Recall proof size m is measured in terms of symbols": Statman's theorem, an $eF$-proof of size $O(m+|\varphi|^2)$ from a Frege proof of $\varphi$ with $m$ steps).
- Paola Bruscoli and Alessio Guglielmi, "On the proof complexity of deep inference", *ACM Transactions on Computational Logic* 10(2):14, 2009, doi:10.1145/1462179.1462186, arXiv:0709.1201v3 (Definition 5.1 and Remark 5.2: the extension variables $A_1,\dots,A_h$ are mutually distinct).
- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001; ECCC report TR98-067, <https://eccc.weizmann.ac.il/report/1998/067/> (Sections 2.1 and 2.3: extended Frege systems are p-equivalent to each other and correspond to $\mathsf{P/poly}$-Frege).
