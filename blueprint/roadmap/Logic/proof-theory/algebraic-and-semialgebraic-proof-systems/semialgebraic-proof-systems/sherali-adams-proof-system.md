# Sherali-Adams proof system

A Sherali-Adams (SA) derivation certifies $p(x) \ge c_0$ from polynomial inequalities over $\{0,1\}^n$ by a static identity: a nonnegative combination of hypotheses and Boolean axioms, each multiplied by a nonnegative junta $\prod_{j \in S} x_j \prod_{k \in T} (1 - x_k)$, equals $p(x) - c_0$; degree is the maximum degree of these products.

Let $\mathcal{P} = \{p_1(x) \ge 0, \dots, p_m(x) \ge 0\}$ be polynomial inequalities over $\mathbb{R}[x_1, \dots, x_n]$. A **Sherali-Adams derivation** of $p(x) \ge c_0$ from $\mathcal{P}$ is a set of polynomials $q_1, \dots, q_\ell$ such that

$$
\sum_{i \in [\ell]} p_i(x) \, q_i(x) = p(x) - c_0 ,
$$

where each $q_i(x) = c_i \prod_{j \in S_i} x_j \prod_{k \in T_i} (1 - x_k)$ is a nonnegative junta with multisets $S_i, T_i \subseteq [n]$ and $c_i \in \mathbb{R}_{\ge 0}$, and each $p_i$ is the constant $1$, a member of $\mathcal{P}$, or one of $x_j^2 - x_j \ge 0$ and $x_j - x_j^2 \ge 0$. A **Sherali-Adams refutation** of $\mathcal{P}$ is a derivation of the constant $-1$. The **degree** of the derivation is $\max_i \{|S_i| + |T_i| + \deg(p_i)\}$ and its **monomial size** is $\sum_i \| p_i q_i \|$, the number of nonzero monomials. A degree-$d$ nonnegative junta is $J_{S,T}(x) = \prod_{i \in S} x_i \prod_{j \in T} (1 - x_j)$ with $S \cap T = \emptyset$ and $|S \cup T| \le d$.

Basic facts:

1. (Soundness and completeness.) There is a degree-$d$ SA refutation of $\mathcal{P}$ if and only if the degree-$d$ Sherali-Adams relaxation $\mathrm{SA}_d(\mathcal{P})$ is infeasible; level $n + \deg(\mathcal{P})$ equals the integer hull.
2. (Resolution, degree.) Let $F$ be an unsatisfiable CNF formula, given to SA as the inequalities $\sum_{i \in S} x_i + \sum_{j \in T} (1 - x_j) - 1 \ge 0$ for its clauses $\bigvee_{i \in S} x_i \vee \bigvee_{j \in T} \neg x_j$. If $F$ has a Resolution refutation of width $w$, then it has an SA refutation of degree at most $w + 2$. No size bound is claimed for SA as defined here: in product form a junta $\prod_{j \in T} x_j \prod_{i \in S} (1 - x_i)$ has $2^{|S|}$ monomials.
3. (Resolution, size, with twin variables.) For Sherali-Adams with twin variables $\bar{x}_j$ (intended to equal $1 - x_j$, with the axiom $x_j + \bar{x}_j - 1 = 0$ and juntas $\prod_{j \in A} x_j \prod_{j \in B} \bar{x}_j$), let $M(C) = \prod_{i \in I} x_i \prod_{j \in J} \bar{x}_j$ be the multiplicative encoding of the clause $C = \bigvee_{i \in I} \neg x_i \vee \bigvee_{j \in J} x_j$. If $C$ has a Resolution derivation of width $k$ and size $s$ from clauses $C_1, \dots, C_m$, then $M(C) = 0$ has a Sherali-Adams proof with twin variables from $M(C_1) = 0, \dots, M(C_m) = 0$ of degree linear in $k$ and size polynomial in $s$ and $k$.

## Proof sketch

The degree bound in fact 2 simulates each resolution step by deriving the junta of the resolvent clause from the juntas of its premises, keeping the degree within the width plus two; with twin variables each junta is a single monomial, which gives the size bound of fact 3. In the static-identity view of Atserias and Ochremiak, Nullstellensatz, Sherali-Adams and positive semidefinite Sherali-Adams are the subsystems of Polynomial Calculus, Lovász-Schrijver and positive semidefinite Lovász-Schrijver in which all applications of the multiplication rule precede all applications of the addition rule; a degree-$d$ proof of the dynamic system with rank $k$ converts to a static proof of degree $d + k$. Every Nullstellensatz proof over the reals is an SA proof. Duality with the LP hierarchy states that the minimum pseudo-expectation of $p$ over degree-$d$ SA pseudo-expectations equals the largest $c_0$ for which $p \ge c_0$ has a degree-$d$ SA derivation. Fleming, Kothari and Pitassi also state, attributing it to Pitassi and Segerlind, a size-degree trade-off: an SA derivation of size $s$ would imply one of degree $O(\sqrt{n \log s} + \deg(\mathcal{P}))$. Atserias and Hakoniemi point out that this claim for Sherali-Adams was made without proof and that the published sketch cannot be turned into a correct proof, so this page does not assert it.

## Depends on

- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)
- [Resolution derivation](../../../propositional-logic/resolution-size-and-width/is-resolution-derivation.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

None.

## Sources

- Noah Fleming, Pravesh Kothari, Toniann Pitassi, "Semialgebraic proofs and efficient algorithm design", *Foundations and Trends in Theoretical Computer Science* 14(1-2), 2019, https://doi.org/10.1561/0400000086; numbering of ECCC report TR19-106, revision 3, 2020 (Definitions 2.7, 2.27 and 2.30, Lemma 2.31, the degree bound of Lemma 2.33 and its proof, Theorems 2.34 and 2.35, Corollary 2.26).
- Albert Atserias, Joanna Ochremiak, "Proof complexity meets algebra", *ACM Transactions on Computational Logic* 20(1), 2019, https://doi.org/10.1145/3265985; numbering of arXiv:1711.07320v2 (Section 2.3, static identities and Sherali-Adams with and without twin variables; Lemma 9).
- Albert Atserias, Tuomas Hakoniemi, "Size-degree trade-offs for sums-of-squares and Positivstellensatz proofs", *34th Computational Complexity Conference (CCC 2019)*, LIPIcs 137, 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.24; numbering of arXiv:1811.01351v2 (Section 1, footnote 1, on the Sherali-Adams size-degree claim).
- Christoph Berkholz, "The relation between polynomial calculus, Sherali-Adams, and sum-of-squares proofs", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, https://doi.org/10.4230/LIPIcs.STACS.2018.11 (Section 2.3, twin variables and Sherali-Adams with twin variables).
