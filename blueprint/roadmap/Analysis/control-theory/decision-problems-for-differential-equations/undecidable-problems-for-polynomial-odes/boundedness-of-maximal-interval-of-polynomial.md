# Boundedness of the maximal interval of polynomial ODEs is undecidable

For an initial-value problem dx/dt = p(t, x), x(t₀) = x₀ with polynomial right-hand side and computable data, no algorithm decides whether the maximal interval on which the solution is defined is bounded; this holds even for one fixed polynomial system of degree at most 56.

**Theorem (Graça, Buescu and Campagnolo).** Consider the initial-value problem

$$
\frac{dx}{dt} = p(t, x), \qquad x(t_0) = x_0,
$$

where $p : \mathbb R^{n+1} \to \mathbb R^n$ has polynomial components and $(t_0, x_0) \in \mathbb R \times \mathbb R^n$, with the coefficients of $p$ and $(t_0, x_0)$ computable. The following problem is undecidable: given such $p$ and $(t_0, x_0)$, decide whether the maximal interval of definition of the solution is bounded.

Moreover, there is a fixed vector $p : \mathbb R^{n+1} \to \mathbb R^n$ of computable polynomials, each component of degree at most $56$, such that it is undecidable, given computable $(t_0, x_0)$, whether the maximal interval of the corresponding initial-value problem is bounded.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof embeds a universal Turing machine into a polynomial initial-value problem whose solution simulates the machine robustly: one component $x_q(t)$ stays at most $m - 11/16$ while the machine (with halting state $m$) has not halted, and is at least $m - 5/16$ after it halts. This simulation result of Graça, Campagnolo and Buescu has no page here. Coupling with $z_1' = x_q - (m - 1/2)$, $z_2' = ((m - 1/2) - x_q) z_2^2$, $z_1(0) = z_2(0) = -1$, the solution exists for all positive time if the machine never halts, while after halting $z_1$ increases at rate at least $3/16$, reaches $0$, and $z_2 = 1/z_1$ blows up, so the maximal interval is bounded exactly when the machine halts. The fixed system of degree at most $56$ comes from a small universal Turing machine with $4$ states and $6$ symbols. The source notes that boundedness is decidable for some subclasses, for instance for linear differential equations.

## Sources

- Daniel S. Graça, Jorge Buescu and Manuel L. Campagnolo, "Boundedness of the domain of definition is undecidable for polynomial ODEs", *Electronic Notes in Theoretical Computer Science* 202, 2008, pp. 49–57 (Proceedings of the Fourth International Conference on Computability and Complexity in Analysis, CCA 2007), <https://doi.org/10.1016/j.entcs.2008.03.007>; read in the authors' copy dated July 2, 2007 at <http://sqig.math.ist.utl.pt/~sqigmath.daemon/pub/GracaDS/07-GBC-bounded.pdf>: Theorem 12 (main statement) with its proof and Theorem 13 (fixed system of degree at most 56) in Section 4 ("The result") of that copy, whose numbering may differ from the journal's.
