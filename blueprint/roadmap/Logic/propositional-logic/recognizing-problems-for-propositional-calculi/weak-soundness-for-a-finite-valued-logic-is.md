# Weak soundness for a finite-valued logic is undecidable

It is undecidable whether all theorems of a given propositional Hilbert-type calculus are tautologies of a given finite-valued logic.

**Theorem (Baaz and Zach).** A *propositional Hilbert-type calculus* $C$ over a propositional language $L$ (variables and finitely many connectives, possibly $0$-ary constants) has a finite set of axioms and a finite set of rules $A_1, \ldots, A_n / B$; its theorems $\mathrm{Thm}(C)$ are the formulas derivable from substitution instances of axioms by substitution instances of rules. An *$m$-valued logic* $M$, a finite deterministic [non-deterministic matrix](non-deterministic-logical-matrices.md), has a finite set $V(M)$ of truth values, a set $V^+(M) \subseteq V(M)$ of designated values and a truth function on $V(M)$ for each connective; $\mathrm{Taut}(M)$ is the set of formulas taking a designated value under every valuation. $C$ is *weakly sound* for $M$ if $\mathrm{Thm}(C) \subseteq \mathrm{Taut}(M)$. There is no algorithm that decides, given a calculus $C$ and a finite-valued logic $M$, whether $C$ is weakly sound for $M$ (Proposition 20 of the source).

The source contrasts weak soundness with two stronger notions in which every axiom is a tautology of $M$: *t-soundness*, where each rule instance with tautological premises has a tautological conclusion, and *strong soundness*, where every valuation satisfying the premises of a rule satisfies its conclusion. The related recognizing problems for calculi with modus ponens and substitution are on [Propositional calculi with modus ponens and substitution](propositional-calculi-with-modus-ponens-and.md).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Non-deterministic logical matrices and their decision problems](non-deterministic-logical-matrices.md)

## Proof depends on

None.

## Expansion

Fix a propositional calculus $C$ with an undecidable set of theorems, which exists by a classical result the source cites, and a formula $F$. Add a new constant $c$ and new constants $c_i$ for the variables $X_i$ of $F$, and let $\sigma$ map $X_i$ to $c_i$, so that $C \vdash F$ iff $C \vdash F\sigma$. Let $C'$ be $C$ with the extra rule $F\sigma / c$, and let $M$ give $c$ a non-designated value and interpret every other connective as a constant function with a designated value. Every formula of the original language other than a variable is then a tautology of $M$ and $c$ is not, so $C'$ is weakly sound for $M$ iff $C' \nvdash c$, that is, iff $C \nvdash F$. A decision procedure for weak soundness would therefore decide theoremhood in $C$.

## Sources

- M. Baaz and R. Zach, "Effective Finite-Valued Approximations of General Propositional Logics", in A. Avron, N. Dershowitz and A. Rabinovich (eds.), *Pillars of Computer Science: Essays Dedicated to Boris (Boaz) Trakhtenbrot on the Occasion of His 85th Birthday*, Lecture Notes in Computer Science 4800, Springer, 2008, pp. 107–129, <https://doi.org/10.1007/978-3-540-78127-1_7>; read as arXiv:1908.01200v1, <https://arxiv.org/abs/1908.01200v1>: Definitions 2, 4, 9, 10 and 17 to 19, Proposition 20 and its proof.
