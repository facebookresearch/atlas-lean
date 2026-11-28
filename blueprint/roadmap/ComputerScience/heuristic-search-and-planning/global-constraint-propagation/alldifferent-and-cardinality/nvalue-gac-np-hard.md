# Generalized arc consistency of NVALUE is NP-hard

The NVALUE constraint fixes the number of distinct values used by a sequence of variables. Deciding whether it has a solution is NP-complete, even when that number is given as a single value, fixed in each instance and different from the number of variables, so enforcing generalized arc consistency on it is NP-hard, although its special case ALLDIFFERENT is polynomial.

Let $X_1,\dots,X_n$ be distinct variables with finite domains and $N$ an integer variable with finite domain. The constraint $\mathrm{NValue}([X_1,\dots,X_n],N)$ allows exactly the assignments with $N=|\{X_1,\dots,X_n\}|$, the number of distinct values taken. With $D(N)=\{n\}$ it is [ALLDIFFERENT](alldifferent-constraint.md).

**Theorem.** NoGACWipeOut on NVALUE is NP-complete under polynomial-time many-one reductions, already restricted to instances in which $D(N)$ is a single value, chosen per instance, smaller than the number of variables. Consequently GACSupport and GACDomain on NVALUE are NP-hard under polynomial-time Turing reductions, and, unless P $=$ NP, no polynomial-time propagator enforces GAC on NVALUE.

The count is part of each instance: the reduction sets $D(N)=\{n\}$ for a formula with $n$ variables, so it does not show hardness for one universal constant value of $N$.

## Depends on

- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): the special case $N=n$.
- [Decision problems of generalized arc consistency](../gac-reasoning-problems.md): NoGACWipeOut, GACSupport and GACDomain, and hardness under polynomial-time Turing reductions (Turing-NP-hardness).
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md): the completeness notion of the first claim.
- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md): the reductions in the completeness claim.
- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md): NP-completeness and NP-hardness.
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md): the conclusion unless P $=$ NP.

## Proof depends on

- [3SAT is NP-complete](../../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-complete.md): the reduction is from 3SAT.
- [Intractability transfers between the GAC decision problems](../gac-intractability-transfer.md): hardness of NoGACWipeOut gives hardness of GACSupport and GACDomain.

## Expansion

Membership in NP is clear (an assignment is a certificate). The reduction is from 3SAT on bitstrings, which accepts encodings of satisfiable CNF formulas with at most three literals per clause. Inputs that do not decode to such a formula go to the fixed no-instance built below from $x_1\wedge\neg x_1$; a formula without clauses goes to the fixed yes-instance built from $x_1$; both have $m=1$ or $m=2$ clauses and lie in the restricted class. Otherwise, rename the variables of the decoded formula to $x_1,\dots,x_n$ ($n\ge0$); with clauses $c_1,\dots,c_m$, $m\ge1$ (an empty clause is allowed and gives an empty domain), build $\mathrm{NValue}([X_1,\dots,X_{n+m}],N)$ with $D(X_i)=\{i,-i\}$ for $i\le n$, $D(X_{n+j})$ the set of literals of $c_j$ (a literal $x$ coded by its index, $\neg x$ by its negative), and $D(N)=\{n\}$. The first $n$ variables always use $n$ distinct values; a solution uses no others, so each clause variable takes a literal already chosen by some $X_i$, and the choices of the $X_i$ define a satisfying assignment. Conversely a satisfying assignment gives a solution. Since $m\ge1$, $D(N)=\{n\}$ is smaller than the number $n+m$ of variables.

The source contrasts this with Régin's GAC algorithm for ALLDIFFERENT, $O(n^{2.5})$ when the number of values is $O(n)$ (in general $O(m\sqrt n)$ for total domain size $m$), and recommends a weaker consistency for NVALUE: bounds consistency on NVALUE can be enforced in polynomial time (citing Bessiere, Hebrard, Hnich, Kiziltan and Walsh, CPAIOR 2005). The same reduction pattern shows NP-hardness of GAC on $\mathrm{Among}$ with variable value sets and on $\mathrm{Common}$ (Theorems 8 and 3 of the source).

## Sources

- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. Theorem 2 (GAC on NValue is NP-hard, even if $N$ is ground and different to $n$) with its proof, and the surrounding discussion of bound consistency on NValue, §4.1 of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
