# Observational equivalence in Reduced ML is undecidable at second-order types

For Reduced ML, a call-by-value higher-order language with finite integers and integer references, deciding whether two closed terms are observationally equivalent is undecidable at every second-order type of arity at least two that has a first-order argument other than the last one, such as $(\mathsf{unit} \to \mathsf{unit}) \to \mathsf{unit} \to \mathsf{unit}$.

**Setting (Cotton-Barratt, Hopkins, Murawski and Ong).** Reduced ML (RML) has base types $\mathsf{unit}$, $\mathsf{int}$ (a finite set of integers) and $\mathsf{intref}$ (integer variables), and function types $\theta \to \theta'$. Its terms include unit and integer constants, successor and predecessor, conditionals on integers, dereferencing $!M$, assignment $M := N$, allocation of references, variables, application, $\lambda$-abstraction, while loops, and $\mathsf{mkvar}$ (building a variable from a reader and a writer); it has a standard big-step call-by-value semantics. The *order* of $\theta \to \theta'$ is $\max(\mathrm{order}(\theta) + 1, \mathrm{order}(\theta'))$, with $\mathsf{unit}$ and $\mathsf{int}$ of order $0$ and $\mathsf{intref}$ of order $1$; its *arity* is $\mathrm{arity}(\theta') + 1$, with $\mathsf{unit}$ and $\mathsf{int}$ of arity $0$ and $\mathsf{intref}$ of arity $1$. Terms $\Gamma \vdash M : \theta$ and $\Gamma \vdash N : \theta$ are *observationally equivalent* if for every closing context $C[-]$ of type $\mathsf{unit}$, $C[M]$ terminates if and only if $C[N]$ terminates. Observational equivalence is *undecidable at* $\theta$ if no algorithm decides it for closed terms of type $\theta$.

**Theorem (Cotton-Barratt, Hopkins, Murawski and Ong).** Observational equivalence of RML terms is undecidable at every second-order type of arity at least two that contains a first-order argument which is not the final argument.

By earlier work, observational equivalence is also undecidable at every third-order type and at every second-order type with at least two first-order arguments, and in each case also for terms with a free variable of type $\theta \to \mathsf{unit}$. The same paper shows that observational equivalence becomes undecidable when recursive functions of type $(\mathsf{unit} \to \mathsf{unit}) \to \mathsf{unit}$ are added to the O-strict fragment, whose observational equivalence is otherwise decidable, and proves decidability for fragments recognized by nested data class memory automata.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proofs use game semantics: observational equivalence coincides with equality of the sets of complete plays of the terms' strategies. The authors build terms of the given type whose complete plays correspond to runs of a Turing-complete machine model, adapting Murawski's proof of undecidability at the type $(\mathsf{unit} \to \mathsf{unit}) \to (\mathsf{unit} \to \mathsf{unit}) \to \mathsf{unit}$ to the type $(\mathsf{unit} \to \mathsf{unit}) \to \mathsf{unit} \to \mathsf{unit}$; this adapts to every type described in the theorem.

## Sources

- Conrad Cotton-Barratt, David Hopkins, Andrzej S. Murawski and C.-H. Luke Ong, "Fragments of ML Decidable by Nested Data Class Memory Automata", Foundations of Software Science and Computation Structures (FoSSaCS 2015), Lecture Notes in Computer Science, pp. 249–263, 2015, <https://doi.org/10.1007/978-3-662-46678-0_16>; Section 2 (RML, order, arity and observational equivalence, and Theorem 1, the game-semantic characterization due to Abramsky and McCusker), and Theorems 4 and 5 of Section 5 ("Undecidable Fragments"), with their proofs in Appendix C (Q-machines and queue programs), of arXiv:1501.04511v1, read at <https://arxiv.org/abs/1501.04511v1>.
