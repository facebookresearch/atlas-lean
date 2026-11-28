# Feasible interpolation for polynomial calculus and Sums-of-Squares

Polynomial calculus over finite fields and Sums-of-Squares over the Boolean cube have a strong feasible interpolation property for equality constraints: from a refutation of $P(x, z) \cup Q(y, z)$ and an assignment $a$ to the shared variables $z$, one finds in polynomial time a refutation of $P(x, a)$ or of $Q(y, a)$.

Let $x, y, z$ be disjoint sequences of variables and $P(x, z)$, $Q(y, z)$ sets of polynomial equations. Polynomial time is measured in the length of the bit-string encoding the given refutation.

**Theorem (polynomial calculus).** For any finite field $\mathbb{F}$ there is a polynomial-time algorithm that, given a PC refutation of $P(x, z) \cup Q(y, z)$ and an assignment $a$ to $z$, outputs a PC refutation of $P(x, a)$ or a PC refutation of $Q(y, a)$. Boolean axioms are not assumed.

**Theorem (Sums-of-Squares).** Let $P(x, z)$ and $Q(y, z)$ be sets of multilinear polynomials over Boolean variables. There is a polynomial-time algorithm that, given an SOS refutation of $P(x, z) \cup Q(y, z)$ over the Boolean hypercube and a Boolean assignment $a$ to $z$, outputs an SOS refutation of $P(x, a)$ or an SOS refutation of $Q(y, a)$ over the Boolean hypercube.

**Feasible disjunction for PC.** If $\Pi$ is a PC refutation of $P(x) \cup Q(y)$ and $S$ is the set of monomials appearing in $\Pi$, then there is a PC refutation of $P(x)$ over the projection $S_x$ or a PC refutation of $Q(y)$ over $S_y$.

## Proof sketch

Both parts use semantic characterizations of refutations restricted to a fixed set of monomials: reduction operators for PC and $\varepsilon$-pseudoexpectations for SOS. If neither side had a refutation over its projected monomial set, the two semantic objects would combine, for PC as $R(m_x m_y) = R^{P}_{S_x}(m_x) R^{Q}_{S_y}(m_y)$, into one that contradicts the given refutation; completeness of the characterization then yields the small refutation. For SOS the difficulty is bit complexity, since low-degree SOS proofs can require coefficients of exponential bit-length (O'Donnell; Raghavendra and Weitz); the given refutation is used to bound the coefficients of the produced one. The same method gives feasible interpolation for Sherali-Adams. SOS cannot have monotone feasible interpolation, because the clique-coloring formulas have small SOS refutations. Feasible interpolation for Resolution and Cutting Planes goes back to Krajíček and Pudlák, and automatability of a system closed under restrictions implies feasible interpolation ([automatability implies interpolation](../../automatability-of-proof-systems/automatability-implies-interpolation.md)).

## Depends on

- [Polynomial calculus](../polynomial-calculus.md)
- [Sums-of-Squares proof system](../sums-of-squares-proof-system.md)
- [Polynomial-time computable functions](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

None.

## Sources

- Tuomas Hakoniemi, "Feasible interpolation for polynomial calculus and sums-of-squares", *47th International Colloquium on Automata, Languages, and Programming (ICALP 2020)*, LIPIcs 168, 2020, https://doi.org/10.4230/LIPIcs.ICALP.2020.63 (Theorems 3, 5, 9 and 14, Lemmas 7 and 8, Section 5).
