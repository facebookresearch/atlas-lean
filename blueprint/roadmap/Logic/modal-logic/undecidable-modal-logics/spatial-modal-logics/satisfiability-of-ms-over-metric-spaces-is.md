# Satisfiability of the logic MS over metric spaces is undecidable

No algorithm decides whether a formula of the logic MS of distance spaces is satisfiable in a model based on a metric space, already when its only distance operators are the punctured circles "somewhere at distance greater than 0 and less than a".

**Theorem.** No algorithm can decide whether a given formula of [MS](the-logic-ms-of-distance-spaces.md) all of whose distance operators are of the form $\exists^{<a}_{>0}$, for natural numbers $a > 0$, is satisfiable in a model based on a metric space.

In particular, satisfiability of MS formulas over metric spaces is undecidable, which Kutz, Wolter, Sturm, Suzuki and Zakharyaschev proved; the survey read states the stronger form above. By contrast, satisfiability of MS formulas in arbitrary distance spaces and in symmetric distance spaces is decidable, by the translation into the two-variable fragment of first-order logic, which can express reflexivity and symmetry but not the triangle inequality.

## Depends on

- [The logic MS of distance spaces](the-logic-ms-of-distance-spaces.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof uses the punctured centers of circles provided by $\exists^{<a}_{>0}$ to enforce the grid $\mathbb N \times \mathbb N$ in models over metric spaces (the source read gives only this idea); a good expansion reconstructs the reduction from the original paper and links the undecidable grid problem that reduction starts from. The triangle inequality is what makes the grid enforceable: without it, in arbitrary or symmetric distance spaces, the problem is decidable. The fragment of MS with only $\exists^{\le a}$ and $\exists^{>a}$ has the finite model property over metric spaces and is EXPTIME-complete under unary coding of the parameters.

## Sources

- O. Kutz, F. Wolter, H. Sturm, N.-Y. Suzuki and M. Zakharyaschev, "Logics of metric spaces", *ACM Transactions on Computational Logic* 4(2):260–294, 2003, <https://doi.org/10.1145/635499.635504>: the original proof of undecidability over metric spaces, cited beside the copy read.
- R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Spatial logic + temporal logic = ?", in *Handbook of Spatial Logics*, Springer, 2007, pp. 497–564, <https://doi.org/10.1007/978-1-4020-5587-4_9>; read in the open-access author copy at <https://kuag19.github.io/homepage/st.pdf>: Section 3.3, Theorem 1.9 (the statement above), the remark on distance spaces following it, and Theorem 1.10.
