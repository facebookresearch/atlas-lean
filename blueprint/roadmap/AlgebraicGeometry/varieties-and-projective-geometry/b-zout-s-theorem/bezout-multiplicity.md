# Bézout's theorem (with multiplicity)

Let $K$ be an algebraically closed field, let
$n \in \mathbb{N}$, and let $f_1, \dots, f_n \in K[X_0, \dots, X_n]$ and integers
$d_1, \dots, d_n \ge 1$ be such that each $f_k$ is homogeneous of degree $d_k$ and has total
degree exactly $d_k$. Suppose the common projective zero set
$Z = V(f_1) \cap \dots \cap V(f_n) \subseteq \mathbb{P}^n(K)$ is finite. Then
$\sum_{p \in Z} i_p(f_1, \dots, f_n) = d_1 d_2 \cdots d_n$ in $\mathbb{N} \cup \{\infty\}$,
where $i_p(f_1, \dots, f_n)$ is the intersection multiplicity of $f_1, \dots, f_n$ at $p$.

The total degree hypothesis rules out $f_k = 0$, which is homogeneous of every degree but has
total degree $0$.

## Sources

- Étienne Bézout, *Théorie générale des équations algébriques*, Paris, 1779. Modern projective formulation: David Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150, Springer, 1995, Chapter 12, or Robin Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Chapter I, Section 7. Listed as §50 in Oliver Knill, *Some Fundamental Theorems in Mathematics*, arXiv:1807.08416 (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `bezout_projective_multiplicity` of the lean-eval benchmark.
