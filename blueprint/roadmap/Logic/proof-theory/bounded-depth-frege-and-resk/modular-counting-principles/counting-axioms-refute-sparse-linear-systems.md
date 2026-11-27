# Counting axioms refute sparse inconsistent linear systems

For a prime $q$, the CNF encoding of an inconsistent system $A\vec x=\vec b$ over $\mathbb Z_q$ with $m$ equations, $n$ variables and at most $w$ variables per equation has constant-depth Frege refutations with counting axioms modulo $q$ of size polynomial in $m$, $n$ and $2^w$.

Fix a prime $q$. Let $A$ be an $m\times n$ matrix over $\mathbb Z_q$ and $\vec b\in\mathbb Z_q^m$ such that $A\vec x=\vec b$ has no solution, and let $w$ be the maximum number of nonzero entries in a row of $A$. For each row $i$ let $C_i$ be a [CNF](../../../propositional-logic/conjunctive-normal-form/cnf.md) in the at most $w$ variables of row $i$, of size at most $2^w$, satisfied by a $0/1$ assignment exactly when $A_i\vec x-b_i=0$ in $\mathbb Z_q$; the *explicit encoding* of $A\vec x=\vec b$ is $\bigwedge_{i=1}^mC_i$.

**Theorem.** There is a constant-depth Frege refutation with [counting axioms modulo $q$](counting-axioms-modulo-m.md) of the explicit encoding of $A\vec x=\vec b$ of size polynomial in $m$, $n$ and $2^w$.

**Corollary.** There is a family of unsatisfiable sets of constant-width clauses that require exponential-size constant-depth Frege refutations but have polynomial-size constant-depth Frege refutations with counting axioms.

## Expansion

Each $C_i$ reduces to the polynomial $p_i=A_i\vec x-b_i$ by a constant-depth reduction, and together the clauses [reduce](reductions-to-polynomial-systems.md) to $\{p_1,\dots,p_m\}$ in size $m2^{O(w)}$. Gaussian elimination gives a degree-one Nullstellensatz refutation of size $O(mn)$, and the [Nullstellensatz simulation](counting-axioms-simulate-nullstellensatz.md) turns it into the claimed refutation. Tseitin formulas on expander graphs are such systems and require exponential-size constant-depth Frege proofs, which gives the corollary; the $\tau$ formulas of Nisan-Wigderson generators built from parity functions are further examples.

## Depends on

- [Counting axioms modulo m](counting-axioms-modulo-m.md)
- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

- [Counting axioms polynomially simulate Nullstellensatz](counting-axioms-simulate-nullstellensatz.md)
- [Reductions from formulas to polynomial systems](reductions-to-polynomial-systems.md)

## Sources

- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (Section 6, theorem on constant-width linear equations and its corollary; Section 5.1, direct translation lemma).
