# Training neural networks with sine activations is undecidable

With the sine function allowed as an activation function, no algorithm decides whether a feedforward network of given architecture can be trained to meet a cost threshold on finitely many rational data points. The problem nevertheless lies in the third level of the arithmetical hierarchy.

**Theorem (Hankala, Hannula, Kontinen and Virtema).** The problem $\mathrm{NN}_{\sin}$-TRAINING, the [neural network training problem](neural-network-training-problem.md) whose activation functions are the identity and $\sin$, is undecidable, and it belongs to the arithmetical class $\Sigma^0_3$.

Instances are finite objects: the architecture, the active edges and neurons, rational data points, a cost function given by an arithmetic expression, the relation symbol and a rational threshold. The hardness reduction of the source produces only instances with relation symbol $=$, threshold $0$, no active neurons (all biases $0$) and a faithful non-negative cost. For the sigmoid activation $\sigma(x) = 1/(1 + e^{-x})$ the same method shows that the training problem is complete for the existential theory of the reals with exponentiation, whose decidability is open (Tarski's exponential function problem).

## Depends on

- [The neural network training problem](neural-network-training-problem.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The result combines two theorems of the source. Theorem 23: for every set $\tau$ of unary real functions, $\mathrm{NN}_\tau$-TRAINING is complete, under polynomial-time reductions, for the class of problems reducible to existential sentences over $(\mathbb{R}, +, \times, <, =, 0, 1)$ extended by $\tau$; the reduction goes through a flat normal form of such sentences (constraints $x = 1$, $x + y + z = 0$, $x \cdot y + 1 = 0$ and $x + f(y) = 0$) and builds a network with zero biases, a faithful non-negative cost, threshold $0$ and equality. Theorem 13: the existential theory of the reals with sine contains $\Sigma^0_1$-hard problems and lies in $\Sigma^0_3$. Hardness holds because the natural numbers are existentially definable with sine. The proof prints $\sin(y) = 0 \wedge 4 < y < 7$, which defines $2\pi$, and $\sin(2\pi x) = 0 \wedge x \ge 0$; the latter defines the non-negative half-integers, not $\mathbb{N}$. With $\pi$ instead, $\sin(y) = 0 \wedge 3 < y < 4$ defines $\pi$ and $\sin(\pi x) = 0 \wedge x \ge 0$ defines $\mathbb{N}$, so Diophantine equations over $\mathbb{N}$ become existential sentences, and the Davis–Putnam–Robinson–Matiyasevich theorem gives $\Sigma^0_1$-hardness. The $\Sigma^0_3$ bound uses rational approximations and the effective continuity of sine. In the source's conventions (existential sentences whose atoms use only $<$, and complexity classes closed under computable reductions), the existential theory with sine without equality atoms is exactly $\Sigma^0_1$ (Theorem 13), with hardness from results of Laczkovich.

A good expansion links Theorem 23 (training is complete for the existential theory of the reals with $\tau$) and Theorem 13 (bounds for the existential theory with sine).

## Sources

- Teemu Hankala, Miika Hannula, Juha Kontinen and Jonni Virtema, "Complexity of Neural Network Training and ETR: Extensions with Effectively Continuous Functions", Proceedings of the AAAI Conference on Artificial Intelligence 38(11), pp. 12278–12285, 2024, <https://doi.org/10.1609/aaai.v38i11.29118>. Read in arXiv:2305.11833v1, <https://arxiv.org/abs/2305.11833v1>; Corollary 25 (the theorem), Theorems 13 and 23, Definition 21 and Corollary 24 (sigmoid), numbering of arXiv:2305.11833v1.
