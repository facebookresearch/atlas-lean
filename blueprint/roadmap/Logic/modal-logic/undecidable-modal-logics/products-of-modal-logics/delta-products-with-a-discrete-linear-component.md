# δ-products with a discrete linear component are Π¹₁-hard

If the horizontal component of a δ-product is a logic of discrete linear orders validated by $(\omega,<)$ and the vertical one has an infinite fan among its frames, the δ-product logic is $\Pi^1_1$-hard, hence not recursively enumerable.

**Theorem (Hampson, Kikot and Kurucz).** Let $L_h$ be a Kripke complete unimodal logic containing $\mathbf{DisK4.3}$ such that $(\omega,<)$ is a frame for $L_h$, and let $L_v$ be a Kripke complete unimodal logic such that some $\omega$-fan is a frame for $L_v$. Then the [δ-product](delta-products-of-modal-logics.md) $L_h \times^\delta L_v$ is $\Pi^1_1$-hard (Theorem 5), and so is its variant over δ-products of rooted frames with equal universes.

Here a frame $(W, R)$ is *modally discrete* if there are no points $x_0, x_1, \dots, x_\infty$ in $W$ with $x_0 R x_1 R x_2 R \cdots$, $x_n R x_\infty$, $x_n \neq x_{n+1}$ and not $x_\infty R x_n$ for all $n < \omega$, and $\mathbf{DisK4.3}$ is the logic of all modally discrete linear orders (Section 6 of the source), and $\Pi^1_1$-hardness refers to the validity problem with the formula as input.

## Depends on

- [Delta-products of modal logics](delta-products-of-modal-logics.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)
- [δ-products with a linear component are undecidable](delta-products-with-a-linear-component-are.md)

## Expansion

The proof modifies that of the linear-component theorem: in a modally discrete horizontal component the generated grid points $x_n$ satisfy $x_n \neq x_{n+1}$, so one can additionally force that a designated control state recurs infinitely often. This reduces the $\Sigma^1_1$-hard recurrence problem for counter machines to satisfiability, so validity is $\Pi^1_1$-hard. A good expansion needs, as a statement prerequisite, the analytical hierarchy ($\Sigma^1_1$ and $\Pi^1_1$ sets) and hardness under many-one reductions, which the statement uses.

## Sources

- Christopher Hampson, Stanislav Kikot and Agi Kurucz, "The decision problem of modal product logics with a diagonal, and faulty counter machines", *Studia Logica* 104(3):455–486, 2016, doi:10.1007/s11225-015-9647-7; read as arXiv:1509.02060v1, <https://arxiv.org/abs/1509.02060v1>: Theorem 5 and its proof sketch in Section 6 of arXiv:1509.02060v1.
