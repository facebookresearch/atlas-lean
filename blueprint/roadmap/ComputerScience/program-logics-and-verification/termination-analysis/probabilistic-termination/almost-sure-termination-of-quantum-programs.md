# Almost-sure termination of quantum while programs is Π⁰₂-complete

For an imperative language mixing classical variables with qubits, Clifford+T gates and measurements, deciding whether a program terminates with probability $1$ from a given state, or from every state, is $\Pi^0_2$-complete.

**Setting (Avanzini, Moser, Péchoux and Perdrix).** Programs are statements over Boolean and natural-number variables and qubit variables:

$$
C ::= \mathtt{skip} \mid x := e \mid C_1; C_2 \mid \mathtt{if}\ b\ \mathtt{then}\ C_1\ \mathtt{else}\ C_2 \mid \mathtt{while}\ b\ \mathtt{do}\ C \mid \bar{q} \mathrel{{*}{=}} U \mid x := \mathtt{meas}(q),
$$

where $e$ and $b$ are arithmetic and Boolean expressions (with $+$, $-$, $\times$, comparisons), $\bar{q} \mathrel{{*}{=}} U$ applies a gate $U$ to a tuple of qubits, and $x := \mathtt{meas}(q)$ measures one qubit in the computational basis, recording the outcome and updating the quantum state. A state $\sigma$ is a classical store with a density matrix. To make the problems computable objects the paper restricts gates to the Clifford+T gates ($I, X, Y, Z, H, S, \mathit{CNOT}, T$) and density matrices to entries in the field of algebraic numbers, each given exactly by a finite representation (the source uses Cohn's representation, a minimal polynomial with an isolating region), under which equality and the order on real algebraic numbers are decidable. A state is thus a finite object: values of the finitely many classical variables in $\mathbb{B}$ and $\mathbb{N}$ (nonnegative integers) and an algebraic density matrix on the qubits. The operational semantics maps a configuration $(C, \sigma)$ to a subdistribution over terminal states; $(C, \sigma)$ is *almost surely terminating*, $(C, \sigma) \in \mathrm{AST}$, if that subdistribution has total mass $1$, and $C \in \mathrm{UAST}$ if $(C, \sigma) \in \mathrm{AST}$ for every such state $\sigma$ (classical store and algebraic density matrix).

**Theorem (Avanzini, Moser, Péchoux and Perdrix).** $\mathrm{AST}$ is $\Pi^0_2$-complete, and $\mathrm{UAST}$ is $\Pi^0_2$-complete.

Completeness is with respect to many-one reductions. The same paper shows that the analogous positive almost-sure termination problems sit at $\Sigma^0_2$ and $\Pi^0_3$.

## Depends on

- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Density matrices, pure states and reduced states](../../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

None.

## Expansion

Membership: $(C, \sigma) \in \mathrm{AST}$ if and only if for every positive real algebraic $\epsilon$ there is $n$ such that the mass terminated within $n$ steps is at least $1 - \epsilon$; that mass is a computable real algebraic number, so the condition is $\forall\exists$ over a decidable relation. Hardness reduces the universal halting problem for classical programs (whether a classical program halts on every input, $\Pi^0_2$-complete): the program that samples $i$ from a geometric distribution (built from fair coins, each a measurement of $H|0\rangle$) and then runs the classical program on the $i$-th input terminates almost surely exactly when the classical program halts on every input. The universal version follows in the same way.

A good expansion links the $\Pi^0_2$-completeness of universal halting for classical programs.

## Sources

- Martin Avanzini, Georg Moser, Romain Péchoux and Simon Perdrix, "On the Hardness of Analyzing Quantum Programs Quantitatively", Programming Languages and Systems (ESOP 2024), Lecture Notes in Computer Science 14577, pp. 31–58, 2024, <https://doi.org/10.1007/978-3-031-57267-8_2>; read in arXiv:2312.13657v1, <https://arxiv.org/abs/2312.13657v1>: Section 2 (syntax and semantics), Sections 3.1–3.3 (computability restrictions, the termination problems, and Theorem 1 with Table 1) and Theorem 5 in Appendix B, in the numbering of that version.
