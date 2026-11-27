# Trajectory reachability for some Beltrami field on Euclidean 3-space is undecidable

There is a Beltrami field u on ℝ³, a stationary solution of the Euler equations with curl u = λu, that simulates a universal Turing machine; consequently it is undecidable whether the trajectory of u through an explicit point meets an explicit open set.

**Theorem (Cardona, Miranda and Peralta-Salas).** A *Beltrami field* is a vector field $u$ on $\mathbb R^3$ with

$$
\operatorname{curl} u = \lambda u
$$

for some constant $\lambda \neq 0$. There exists a Beltrami field $u$ on $\mathbb R^3$ that is [Turing complete](turing-complete-vector-fields.md) (it can simulate a universal Turing machine). Consequently it is undecidable to determine whether the trajectory of $u$ through an explicit point meets an explicit open set of $\mathbb R^3$.

The field is fixed; the points and open sets of the definition of Turing completeness vary with the machine, its input and the prescribed output. The proof gives such a field for every $\lambda \neq 0$. The field is defined with respect to the Euclidean metric but does not have finite energy, and all the simulated computations take place on the invariant plane $\{z = 0\}$, which is not compact.

## Depends on

- [Turing complete vector fields](turing-complete-vector-fields.md)
- [Smooth vector fields](../../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/smooth-vector-field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof constructs a smooth function $f$ on $\mathbb R^2$ whose gradient field is Turing complete in a robust way, approximates $f$ by an entire function $F$ so closely that $\nabla_{\mathbb R^2} F$ is still Turing complete, and then extends $\nabla_{\mathbb R^2} F$ to a Beltrami field $u$ on all of $\mathbb R^3$ with $u(x, y, 0) = \partial_x F\, \partial_x + \partial_y F\, \partial_y$, by a global Cauchy–Kovalevskaya theorem for the curl operator proved in the same paper for entire Cauchy data. The plane $\{z = 0\}$ is invariant under the flow of $u$, so $u$ inherits Turing completeness, and the undecidability of the halting problem gives the undecidable trajectories. Earlier Turing complete steady Euler flows in dimension $3$ used a metric adapted to the construction rather than the Euclidean one.

## Sources

- Robert Cardona, Eva Miranda and Daniel Peralta-Salas, "Computability and Beltrami fields in Euclidean space", *Journal de Mathématiques Pures et Appliquées* 169, 2023, pp. 50–81, <https://doi.org/10.1016/j.matpur.2022.11.007>; read as arXiv:2111.03559v3, <https://arxiv.org/abs/2111.03559v3>: Theorem 1 of that version, the definition of Beltrami fields in Section 1, the remark on undecidable trajectories in Section 2, and the proof of Theorem 1 in Section 5 (with the global Cauchy–Kovalevskaya theorem of Section 3 and the Turing complete gradient field of Section 4).
