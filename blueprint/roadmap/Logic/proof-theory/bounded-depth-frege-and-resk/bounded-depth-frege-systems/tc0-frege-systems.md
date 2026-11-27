# TC$^0$-Frege (threshold logic)

TC$^0$-Frege is the sequent calculus whose formulas use negation and unbounded threshold connectives $\mathsf{Th}_i$, where $\mathsf{Th}_i(A_1,\dots,A_n)$ holds when at least $i$ arguments are true, and whose proofs of a family must keep all formulas within one constant depth.

**Formulas.** TC$^0$ formulas are built from the constants $\bot,\top$ and variables $p_i$ using $\neg$ and, for $n>1$ and $i\in\mathbb N$, the connective $\mathsf{Th}_i A_1\dots A_n$. Semantically $\mathsf{Th}_i(A_1,\dots,A_n)$ is true if and only if at least $i$ of the $A_k$ are true; thus $\mathsf{Th}_n$ is an $n$-ary conjunction, $\mathsf{Th}_1$ is an $n$-ary disjunction, $\mathsf{Th}_0(A_1,\dots,A_n)=\top$ and $\mathsf{Th}_i(A_1,\dots,A_n)=\bot$ for $i>n$. The depth of a formula is its maximal nesting of connectives and its size is its number of connectives.

**Proofs.** TC$^0$-Frege is a sequent calculus with axioms $A\longrightarrow A$, $\bot\longrightarrow$ and $\longrightarrow\top$, the weakening, exchange and contraction rules on both sides, the two $\neg$ rules, cut, introduction rules for $\mathsf{Th}_n$ (all arguments) and $\mathsf{Th}_1$ (some argument), and the general threshold rules

$$
\frac{\mathsf{Th}_iA_2\dots A_n,\Gamma\longrightarrow\Delta\qquad \mathsf{Th}_{i-1}A_2\dots A_n,A_1,\Gamma\longrightarrow\Delta}{\mathsf{Th}_iA_1\dots A_n,\Gamma\longrightarrow\Delta}
$$

$$
\frac{\Gamma\longrightarrow\mathsf{Th}_iA_2\dots A_n,A_1,\Delta\qquad \Gamma\longrightarrow\mathsf{Th}_{i-1}A_2\dots A_n,\Delta}{\Gamma\longrightarrow\mathsf{Th}_iA_1\dots A_n,\Delta}
$$

A proof of $\varphi$ is a sequence of sequents ending in $\longrightarrow\varphi$; its size is the total size of its formulas and its depth the maximal depth of a formula in it. A TC$^0$-Frege proof of a family $\{\varphi_i\}$ is a family of such proofs with a common constant bounding the depth of every formula in all of them. The system is sound and complete: it proves exactly the tautologies.

## Expansion

Different formulations of TC$^0$-Frege (threshold logic) polynomially simulate each other, so the precise rule set is not important. TC$^0$-Frege polynomially simulates resolution and bounded-depth Frege and is strictly stronger than both: it has polynomial-size proofs of the pigeonhole principle, which require exponential size in resolution ([Haken](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)) and superpolynomial size in bounded-depth Frege (Ajtai). Frege and extended Frege polynomially simulate TC$^0$-Frege. It also [refutes most dense random 3CNFs in polynomial size](../k-dnf-resolution-and-random-cnf/tc0-frege-refutes-dense-random-3cnf.md).

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sebastian Müller and Iddo Tzameret, "Short propositional refutations for dense random 3CNF formulas", *Annals of Pure and Applied Logic*, 2014, https://doi.org/10.1016/j.apal.2014.08.001; numbering as in arXiv:1101.3970v2 (Definitions 2.3 and 2.4, Proposition 2.5, Section 1.1).
