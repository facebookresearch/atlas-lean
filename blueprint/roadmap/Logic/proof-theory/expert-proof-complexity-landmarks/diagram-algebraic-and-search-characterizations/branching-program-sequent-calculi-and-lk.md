# Branching-program sequent calculi are quasipolynomially equivalent to LK

The sequent calculi eLDT and eLNDT, whose lines are sequents of decision trees made dag-like by extension variables (deterministic and nondeterministic branching programs, the nonuniform analogues of L and NL), polynomially simulate the Gentzen calculus LK and are quasipolynomially simulated by it.

**Decision tree formulas.** DT formulas are generated from literals by the case connective: if $A, B$ are DT formulas and $p$ is a literal, then $(A\,p\,B)$ is a DT formula, read "if $p$ is false then $A$, else $B$". NDT formulas also allow $(A \vee B)$. The size of a formula is its number of occurrences of atoms. A sequent $\Gamma \to \Delta$ of multisets of formulas is true under an assignment iff some formula of $\Gamma$ is false or some formula of $\Delta$ is true.

**The systems.** LDT is the sequent calculus on DT formulas with initial sequents $p \to p$, $p, \bar{p} \to$ and $\to p, \bar{p}$ for literals $p$, the contraction, weakening and cut rules, and the two decision rules

$$
\frac{\Gamma, A \to p, \Delta \qquad \Gamma, p, B \to \Delta}{\Gamma, (A\,p\,B) \to \Delta}
\qquad
\frac{\Gamma \to A, p, \Delta \qquad \Gamma, p \to B, \Delta}{\Gamma \to (A\,p\,B), \Delta}.
$$

LNDT is LDT on NDT formulas with the two $\vee$ rules of LK added. Proofs are dag-like and their size is the total size of the formula occurrences. For eDT (eNDT) formulas, extension variables $e$ may also occur as formulas but never as decision literals; a set of extension axioms $\{e_i \leftrightarrow A_i\}_{i<n}$, where $A_i$ mentions only $e_j$ with $j < i$, is identified with the sequents $e_i \to A_i$ and $A_i \to e_i$. An **eLDT proof** is a pair $(\pi, \mathcal{A})$ of such a set of eDT extension axioms and an LDT derivation $\pi$ that may use the sequents of $\mathcal{A}$ as initial sequents; **eLNDT** is the same with eNDT formulas and LNDT derivations. A branching program becomes an eDT formula by naming each internal node with an extension variable, and conversely.

**Theorem.**

1. eLDT, and hence also eLNDT, polynomially simulates LK.
2. LK quasipolynomially simulates eLNDT, and hence also eLDT.

Here a simulation is a procedure mapping a proof in one system to a proof in the other of the translated sequent: Boolean formulas are translated into eDT formulas through the extension-based conjunction and disjunction constructions, and eNDT formulas into Boolean formulas that evaluate the nondeterministic branching program they represent; "quasipolynomially" means time $n^{O(\log n)} = 2^{O(\log^2 n)}$.

## Expansion

For part 1, the LK proof is first put in balanced form, so that every formula has depth $O(\log n)$; each formula occurrence is replaced by an eDT formula built with the constructions $\mathrm{And}(A, B)$ and $\mathrm{Or}(A, B)$, which redirect the $1$-leaves (respectively $0$-leaves) of a copy of the program for $A$, including inside renamed copies of its extension axioms, to $B$. Logarithmic nesting keeps the number of new extension variables polynomial, and each LK step is simulated by cuts against short, cut-free proofs of the truth conditions of $\mathrm{And}$ and $\mathrm{Or}$ (Lemma 27). For part 2, NL predicates have Boolean formulas of size $n^{O(\log n)}$: an evaluator for nondeterministic branching programs is built from quasipolynomial-size formulas for st-connectivity whose basic properties have quasipolynomial-size LK proofs, and each eLNDT step is simulated by cutting against proofs of its truth conditions. At the bottom of the hierarchy the paper also proves that LDT is polynomially equivalent to the depth-one fragment 1-LK, that tree-like LNDT is polynomially equivalent to LDT on DT sequents, and that LNDT is polynomially equivalent to the depth-two fragment 2-LK.

## Depends on

- [Cut elimination for the classical sequent calculus LK](../../../proof-theory/cut-elimination-for-the-classical-sequent-calculus.md)
- [Cook-Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Anupam Das, Alexander Knop, "Proof Complexity of Systems of (Non-Deterministic) Decision Trees and Branching Programs", *28th EACSL Annual Conference on Computer Science Logic (CSL 2020)*, LIPIcs, 2020, doi:10.4230/LIPIcs.CSL.2020.12 (Definitions 1, 3, 4, 15, 16, 19, 20, 21 and 24; Theorems 29 and 30; Lemma 27; Theorems 13, 14, 17 and 18 for the lower systems).
