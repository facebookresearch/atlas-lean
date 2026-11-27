# With new variables, DRAT and PR are equivalent to extended resolution

When new variables are allowed, all the clausal redundancy systems BC, RAT, SPR, PR, SR and their deletion variants DBC, DRAT, DSPR, DPR, DSR are polynomially equivalent to extended resolution.

**Theorem (Buss–Thapen; Kullmann; Kiesl, Rebola-Pardo and Heule; Heule and Biere).** [Extended resolution](../../../propositional-logic/sat-solving/extended-resolution.md) p-simulates DSR, and hence every system BC, RAT, SPR, PR, SR, DBC, DRAT, DSPR, DPR, DSR. Conversely BC, and therefore each of these systems, p-simulates extended resolution. In particular DRAT and extended resolution p-simulate each other.

Moreover, the canonical disjoint NP pair $(\mathrm{REF}(P),\mathrm{SAT})$ of extended resolution is many-one reducible in both directions to the canonical pair of each of these systems and of their variants without new variables. Here $\mathrm{REF}(P)$ is the set of pairs $(\Gamma,1^m)$ such that $\Gamma$ has a $P$-refutation of length at most $m$, and $\mathrm{SAT}$ is the set of pairs $(\Gamma,1^m)$ with $\Gamma$ satisfiable and $m\ge 1$. A disjoint NP pair is a pair $(U,V)$ of disjoint NP sets, and a many-one reduction from $(U,V)$ to $(U',V')$ is a polynomial-time function mapping $U$ into $U'$ and $V$ into $V'$.

## Expansion

*BC simulates ER.* Buss and Thapen take extended resolution with extension steps for definitions $x\leftrightarrow(p\wedge q)$, the case of Tseitin's definitions on the extended resolution page up to writing the new literal negated. An extension step introducing $x\leftrightarrow(p\wedge q)$ adds the clauses $x\vee\bar p\vee\bar q$, $\bar x\vee p$, $\bar x\vee q$ one at a time; each is blocked on $x$ because $x$ is new and the resolvents on $x$ with the previously added extension clauses are tautological.

*ER simulates DSR.* For an SR step adding $C$ to $\Gamma_i$ with witness $\tau$, introduce for every variable $x_j$ a new variable $x'_j$ with the extension axiom $x'_j\leftrightarrow(x_j\wedge C)\vee(\tau(x_j)\wedge\neg C)$; resolution then derives the renamed clause set $\Gamma_{i+1}(\vec x/\vec x')$ from $\Gamma_i$, mirroring the semantic argument $\pi\mapsto\pi\circ\tau$. Alternatively, $S^1_2$ proves the soundness of DSR by $\Sigma^b_1$ length induction, and the propositional translation of this proof yields polynomial-size extended resolution proofs of the soundness statement. For the canonical pairs, a refutation size $m$ in ER is matched by adding to $\Gamma$ the set $X^m$ of the two clauses $y\vee x_1\vee\dots\vee x_m$ and $y$ in fresh variables, which let BC$^-$ emulate $m$ extension variables (Lemma 2.2); setting $y=1$ restricts $\Gamma\cup X^m$ back to $\Gamma$. The p-simulation of DRAT by extended resolution is also recorded, with an $O(P^4)$ size bound, as [extended resolution polynomially simulates DRAT](../../../propositional-logic/sat-solving/extended-resolution-simulates-drat.md).

## Depends on

- [DRAT, PR and related clausal proof systems](drat-and-pr-proof-systems.md)
- [Extended resolution](../../../propositional-logic/sat-solving/extended-resolution.md)
- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Blocked, RAT, propagation-redundant and substitution-redundant clauses](propagation-and-substitution-redundancy.md)

## Sources

- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Example 1.8 and Section 2.1: BC simulates extended resolution and Theorem 2.1, ER simulates DSR; Section 2.2: Lemma 2.2; Section 2.3: Definition 2.6 of disjoint NP pairs and many-one reductions, Definition 2.7 of $\mathrm{SAT}$ (with $m\ge 1$), $\mathrm{REF}(P)$ and canonical NP pairs, and Theorem 2.8).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: RAT inferences simulate the extension rule and extended resolution simulates RAT, so DRAT and extended resolution polynomially simulate each other).
