# Turing complete vector fields

A vector field is called Turing complete when the halting of every Turing machine on every input, with a prescribed piece of output, is equivalent to an explicit trajectory meeting an explicit open set.

**Turing machines (recalled).** A Turing machine is given by a finite set $Q$ of states with an initial state $q_0$ and a halting state $q_{\mathrm{halt}}$, a finite alphabet $\Sigma$ with at least two symbols, and a transition function $\delta : Q \times \Sigma \to Q \times \Sigma \times \{-1, 0, 1\}$; it runs on a bi-infinite tape $t = (t_n)_{n \in \mathbb Z} \in \Sigma^{\mathbb Z}$ in the usual way and halts when it enters $q_{\mathrm{halt}}$.

**Turing complete vector fields.** A vector field $X$ on a manifold $M$ is called *Turing complete* if for every integer $k \ge 0$, every Turing machine $T$, every input tape $t$ and every finite string $(t^*_{-k}, \ldots, t^*_k)$ of symbols, there are an explicitly constructible point $p \in M$ and an open set $U \subseteq M$ such that the positive trajectory of $X$ through $p$ meets $U$ exactly when $T$ halts on input $t$ with an output tape whose positions $-k, \ldots, k$ carry $t^*_{-k}, \ldots, t^*_k$. "Explicitly constructible" means computable: the point and the open set can be determined to arbitrary precision by a Turing machine. The same definition applies to diffeomorphisms.

## Depends on

- [Smooth vector fields](../../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/smooth-vector-field.md)

## Proof depends on

None.

## Expansion

Because the halting problem is undecidable, a Turing complete vector field has trajectories with undecidable long-term behavior: no algorithm decides, for the explicit points and open sets of the definition, whether the trajectory through the point meets the open set. The definition follows Moore; the analogous notion for the Euler equations as an infinite-dimensional dynamical system is [Turing completeness of the Euler equations](turing-complete-euler-equations.md). In some constructions the point depends only on $T$ and $t$ and the open set only on the output string (as in Tao's notion), in others the open set is fixed and the point depends on all the data; both give the same computational power.

## Sources

- Robert Cardona, Eva Miranda and Daniel Peralta-Salas, "Turing universality of the incompressible Euler equations and a conjecture of Moore", *International Mathematics Research Notices* 2022(22), 2022, pp. 18092–18109, <https://doi.org/10.1093/imrn/rnab233>; read as arXiv:2104.04356v1, <https://arxiv.org/abs/2104.04356v1>: Section 2 of that version (Turing machines, Definition 2.1 of Turing complete vector fields, the comparison with Tao's notion, and Remark 2.2 on undecidable trajectories).
- Robert Cardona, Eva Miranda and Daniel Peralta-Salas, "Computability and Beltrami fields in Euclidean space", *Journal de Mathématiques Pures et Appliquées* 169, 2023, pp. 50–81, <https://doi.org/10.1016/j.matpur.2022.11.007>; read as arXiv:2111.03559v3, <https://arxiv.org/abs/2111.03559v3>: Definition 7 in Section 2 of that version (Turing complete vector fields, with $k \ge 0$ and orbits taken for positive times) and the paragraph after it on the meaning of "explicitly constructible".
