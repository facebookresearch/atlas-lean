# Continuous linear functionals on the space of all real functions

Let $H$ be a set and give
the space $\mathbb{R}^H$ of all real-valued functions on $H$ the topology of pointwise
convergence. Then for every continuous linear functional $f \colon \mathbb{R}^H \to \mathbb{R}$
there are a natural number $n$, points $t_1, \dots, t_n \in H$ and real numbers
$\alpha_1, \dots, \alpha_n$ such that $f(x) = \sum_{i=1}^n \alpha_i \, x(t_i)$ for every
$x \in \mathbb{R}^H$. The statement is universe-polymorphic: $H$ may be a type in any
universe, not only in `Type`.

This is the version of Problem 10 of the Scottish Book for functionals that are continuous in
this topology, the product topology. The typescript defines the pointwise convergence of
sequences in $\mathbb{R}^H$ and then states the theorem for each linear functional, with no
continuity qualification; for an arbitrary set $H$, continuity in the product topology cannot
simply be read off that sequential formulation. Without any continuity hypothesis the claim is
false: when $H$ is infinite, the algebraic dual of $\mathbb{R}^H$ is strictly larger than the
span of the evaluations.

## Sources

- S. Banach and S. Mazur, Problem 10 of the Scottish Book, stated as a theorem in the Scottish Book typescript.
