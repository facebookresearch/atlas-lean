# Positive almost-sure termination of quantum while programs is Σ⁰₂-complete

For the same mixed classical–quantum while language, deciding whether a program has finite expected running time from a given state is $\Sigma^0_2$-complete, and deciding it for every initial state is $\Pi^0_3$-complete.

**Setting.** As in [almost-sure termination of quantum while programs](almost-sure-termination-of-quantum-programs.md): imperative programs over classical variables and qubits with Clifford+T gates, computational-basis measurements, and density matrices with algebraic entries. A configuration $(C, \sigma)$ is *positively almost surely terminating*, $(C, \sigma) \in \mathrm{PAST}$, if its expected derivation length (the expected number of reduction steps until termination) is finite, and $C \in \mathrm{UPAST}$ if $(C, \sigma) \in \mathrm{PAST}$ for every state $\sigma$. Every positively almost surely terminating configuration is almost surely terminating, and not conversely.

**Theorem (Avanzini, Moser, Péchoux and Perdrix).** $\mathrm{PAST}$ is $\Sigma^0_2$-complete, and $\mathrm{UPAST}$ is $\Pi^0_3$-complete.

## Depends on

- [Almost-sure termination of quantum while programs is Π⁰₂-complete](almost-sure-termination-of-quantum-programs.md)
- [The arithmetical class Σₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

Membership: $(C, \sigma) \in \mathrm{PAST}$ if and only if there is a bound $c$ such that for every $n$ the expected derivation length truncated at $n$ steps is below $c$, an $\exists\forall$ condition over a decidable relation; quantifying over all states adds one universal quantifier for $\mathrm{UPAST}$. Hardness adapts the reductions of Kaminski and Katoen for probabilistic programs, simulating each fair coin by measuring a qubit prepared in $H|0\rangle$.

## Sources

- Martin Avanzini, Georg Moser, Romain Péchoux and Simon Perdrix, "On the Hardness of Analyzing Quantum Programs Quantitatively", Programming Languages and Systems (ESOP 2024), Lecture Notes in Computer Science 14577, pp. 31–58, 2024, <https://doi.org/10.1007/978-3-031-57267-8_2>; Section 3 (the termination problems and the completeness theorem with its table) and the PAST theorem in Appendix B of arXiv:2312.13657v1, <https://arxiv.org/abs/2312.13657v1>.
