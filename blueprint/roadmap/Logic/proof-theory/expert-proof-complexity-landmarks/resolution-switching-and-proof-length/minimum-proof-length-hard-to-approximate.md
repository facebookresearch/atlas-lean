# NP-hardness of approximating minimum proof length

Unless P = NP, no polynomial-time algorithm finds resolution refutations within a factor $2^{\log^{1-o(1)}n}$ of the shortest, even for Horn clauses, tree-like or dag-like, by steps or symbols. The same holds for every Frege and extended Frege system, the sequent calculus with or without cut, and the polynomial calculus.

**Problems.** *Minimum Step-Length* (respectively *Symbol-Length*) *Resolution Refutation*: given an unsatisfiable set $\Gamma$ of clauses, find a resolution refutation of $\Gamma$ minimizing its number of clauses (respectively the sum of the sizes of its clauses). *Minimum Length* (respectively *Step-Length*) *Frege Proof*, for a fixed Frege system $F$: given a tautology $\varphi$, find an $F$-proof of $\varphi$ minimizing its number of symbols (respectively lines). An algorithm *approximates* such a problem within a factor $\alpha$ (a constant or a function of the input length) if on every instance it outputs a solution of length at most $\alpha$ times the minimum. Algorithms are measured against the length of the shortest proof of the input, not only the input size. *Circuit MMSA* (monotone minimum satisfying assignment) asks, for a monotone circuit $C$ over $\{\wedge,\vee\}$, for a satisfying input assignment with the fewest variables set to true.

**Theorem.** Suppose P $\ne$ NP. Then no polynomial-time algorithm approximates Minimum Step-Length Resolution Refutation, or Minimum Symbol-Length Resolution Refutation, within a factor

$$
2^{\log^{1-o(1)}n},
$$

where $n$ is the input size. This holds for dag-like and for tree-like refutations, and already when the input clauses are Horn clauses (at most one positive literal each). The same non-approximability holds for:

1. the Minimum Length and Minimum Step-Length Frege Proof problems for every Frege system, dag-like or tree-like, and likewise for extended Frege systems;
2. minimum length proofs in the propositional sequent calculus and in the cut-free propositional sequent calculus;
3. minimum size polynomial calculus refutations.

## Expansion

All cases reduce from Circuit MMSA, which Dinur and Safra showed cannot be approximated within $2^{\log^{1-o(1)}n}$ in polynomial time unless P = NP, by A-reductions (polynomial-time reductions that preserve the approximation ratio up to a constant factor). For resolution, number the subcircuits $C_1,\dots,C_L$ of $C$ bottom-up with output $C_L$ and use variables $y_i$ with clauses $\{\neg y_L\}$, $\{\neg y_j,\neg y_k,y_i\}$ for each AND gate $C_i=C_j\wedge C_k$, and $\{\neg y_j,y_i\}$, $\{\neg y_k,y_i\}$ for each OR gate. Each input $x_i$ gets a chain of fresh variables $x_{i,1},\dots,x_{i,m}$ with clauses $\{x_{i,1}\}$, $\{\neg x_{i,j},x_{i,j+1}\}$ and $\{\neg x_{i,m},y_i\}$, so deriving $y_i$ costs $m$ steps. All clauses are Horn and the set is unsatisfiable because $C$ is monotone. If the minimum satisfying assignment of $C$ sets $\ell$ inputs true, there is a dag-like refutation of symbol-length $O(\ell m+n)$ and a tree-like one of step-length $O(\ell m+n)$ and symbol-length $O(\ell m+n^2)$, while every refutation has step-length at least $\ell m$: the inputs whose whole chains are used form a satisfying assignment, otherwise a truth assignment would satisfy every clause used. With $m=n^3$ the minimum refutation length is within a constant factor of $\ell m$, so approximating it approximates $\ell$.

For a Frege system the inputs of the tautology $\bigwedge_i((x_{j_{i,1}}\,\mathrm{OP}\,x_{j_{i,2}})\to x_i)\to x_n$ are replaced by independent tautologies $\bot\vee(\bot\vee\cdots(\bot\vee(\neg p_i\vee p_i))\cdots)$ of nesting depth $m$, translated into the system's connectives. The lower bound counts *active* subformulas: let $I$ be the set of inputs all of whose $m$ nested layers are active in the proof; replacing an inactive layer of every other input by $\bot$ leaves a valid proof, so the resulting formula is still a tautology, which forces $I$ to satisfy $C$ and hence $|I|\ge\ell$; active formulas bound the symbol length and the step length from below up to constants depending on the system, and these bounds also hold for extended Frege. The polynomial calculus simulates the width-3 resolution upper bound line by line and inherits the resolution lower bound argument. When the shortest proofs may be superpolynomial and the algorithm must run in time polynomial in the formula alone, the paper shows that, unless NP $\subseteq$ P/poly, no polynomial-time algorithm approximates the minimum refutation length within any polynomial factor for proof systems whose maximum refutation length has smooth superpolynomial growth, which includes resolution.

An automatable system could be approximated within a polynomial factor, so these super-linear factors are a weaker conclusion than non-automatability, but under the minimal assumption P $\ne$ NP; compare the [Atserias–Müller theorem](../../../proof-theory/automatability-of-proof-systems/atserias-muller.md), which shows that finding resolution refutations of size polynomial in the optimum is NP-hard.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Cook-Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Michael Alekhnovich, Sam Buss, Shlomo Moran, Toniann Pitassi, "Minimum Propositional Proof Length is NP-Hard to Linearly Approximate", *Journal of Symbolic Logic*, 2001, doi:10.2307/2694916 (Section 1 problem definitions; Theorem 4; Theorem 5 and Corollary 6 for resolution, with Lemmas 7 and 8; Theorem 12, Corollary 13, Lemmas 15 to 18 and the Remark after Lemma 18 for Frege and extended Frege; Theorems 19 and 20 for the sequent calculi; Lemmas 21 and 22 and Theorem 23 for the polynomial calculus; Theorem 24 for long proofs).
