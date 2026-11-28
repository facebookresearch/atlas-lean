# Twelve mixed quantifier prefixes over integer Diophantine equations are undecidable

For each of the quantifier prefixes $\forall\exists^7$, $\forall^2\exists^4$, $\exists\forall\exists^4$, $\exists\forall^2\exists^3$, $\exists^2\forall\exists^3$ and seven others, no algorithm decides, for an arbitrary integer polynomial, whether the sentence with that prefix in front of the equation $P = 0$ is true over $\mathbb{Z}$.

For quantifiers $\rho_1, \dots, \rho_n \in \{\forall, \exists\}$, say that *$\rho_1 \cdots \rho_n$ over $\mathbb{Z}$ is undecidable* when there is no algorithm that decides, for an arbitrary polynomial $P(x_1, \dots, x_n) \in \mathbb{Z}[x_1, \dots, x_n]$, whether

$$
\rho_1 x_1 \cdots \rho_n x_n \; \bigl( P(x_1, \dots, x_n) = 0 \bigr)
$$

holds, all variables ranging over $\mathbb{Z}$. Say that *$\rho_1 \cdots \rho_n$ over $\mathbb{Z}$ with $\forall$ bounded* is undecidable when the same holds after each universal quantifier $\forall x_j$ is replaced by $\forall x_j \in [P_j, Q_j]$, where $P_j$ and $Q_j$ are integer polynomials in the existentially quantified variables $x_i$ with $i < j$, given as part of the input together with $P$. Write $\forall^k$ and $\exists^k$ for blocks of $k$ equal quantifiers.

**Theorem (Sun).**

1. Each of the prefixes
   $\forall\exists^7$, $\forall^2\exists^4$, $\exists\forall\exists^4$, $\exists\forall^2\exists^3$, $\exists^2\forall\exists^3$, $\forall\exists\forall\exists^3$, $\forall\exists^2\forall^2\exists^2$, $\forall^2\exists\forall^2\exists^2$, $\forall\exists\forall^3\exists^2$, $\exists^2\forall^3\exists^2$, $\exists\forall\exists\forall^2\exists^2$, $\exists\forall^6\exists^2$
   over $\mathbb{Z}$ is undecidable.
2. Each of the prefixes
   $\exists\forall\exists^4$, $\exists\forall^2\exists^3$, $\exists^2\forall\exists^3$, $\exists^2\forall^2\exists^2$, $\exists\forall\exists\forall\exists^2$, $\exists\forall^5\exists^2$
   over $\mathbb{Z}$ with $\forall$ bounded is undecidable.

Conventions: undecidability of a prefix passes to every prefix containing it as a subsequence, so clause 1 is a list of specific prefixes, not of all prefixes of that length. The source conjectures that $\forall^2 \exists^2$ over $\mathbb{Z}$ is undecidable; that case is not part of the theorem.

## Depends on

None.

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For a recursively enumerable set $A \subseteq \mathbb{N}$, Sun constructs representations of $A$, or of its complement, by integer polynomials under each listed prefix: for instance, $A$ has an $\exists^2 \forall \exists^3$-representation over $\mathbb{Z}$, so that $a \in A$ exactly when $\exists x_1 \exists x_2 \forall x_3 \exists x_4 \exists x_5 \exists x_6 \; P(a, x_1, \dots, x_6) = 0$, and the complement of $A$ has a $\forall^2 \exists^4$-representation. The constructions rest on an auxiliary representation theorem for recursively enumerable sets proved in the source, combined with ways of expressing sign conditions and inequalities over $\mathbb{Z}$ by few quantified variables. Taking $A$ recursively enumerable but not recursive, and substituting each fixed $a$, an algorithm for the prefix would decide membership in $A$.

## Sources

- Zhi-Wei Sun, *Mixed quantifier prefixes over Diophantine equations with integer variables*, J. Syst. Sci. Complex. 38 (2025), no. 5, 2226–2251, https://doi.org/10.1007/s11424-024-4159-z, read in the copy arXiv:2103.08302v3: the statement is Theorem 1.1 there, derived from the representation theorems 1.2, 1.3 and 1.4 of that version; the definitions are in its introduction.
