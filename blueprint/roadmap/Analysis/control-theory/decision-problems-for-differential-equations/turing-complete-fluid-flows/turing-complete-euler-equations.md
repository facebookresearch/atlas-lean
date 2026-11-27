# Turing complete Euler equations

The system of incompressible Euler equations on a compact Riemannian manifold is called Turing complete when the halting of every Turing machine on every input, with a prescribed piece of output, is equivalent to the solution with an explicit initial datum being smooth for all time and entering an explicit open set of divergence-free vector fields.

**Setting.** Let $(M, g)$ be a compact orientable Riemannian manifold without boundary, and let $\mathfrak X^\infty_{\mathrm{vol}}(M)$ be the space of smooth divergence-free vector fields on $M$ with the Whitney $C^\infty$ topology. The incompressible Euler equations for a time-dependent field $X$ and pressure $P$ are

$$
\partial_t X + \nabla_X X = -\nabla P, \qquad \operatorname{div} X = 0, \qquad X|_{t = 0} = X_0 .
$$

**Definition.** The Euler equations on $(M, g)$ are called *Turing complete* if for every integer $k > 0$, every Turing machine $T$, every input tape $t$ and every finite string $(t^*_{-k}, \ldots, t^*_k)$ of symbols of its alphabet, there are an explicitly constructible $X_0 \in \mathfrak X^\infty_{\mathrm{vol}}(M)$ and a constructible open set $U \subseteq \mathfrak X^\infty_{\mathrm{vol}}(M)$ such that the solution of the Euler equations with initial datum $X_0$ is smooth for all time and meets $U$ exactly when $T$ halts on input $t$ with an output tape whose positions $-k, \ldots, k$ carry $t^*_{-k}, \ldots, t^*_k$. Turing machines and explicit constructibility are as for [Turing complete vector fields](turing-complete-vector-fields.md).

## Depends on

- [Turing complete vector fields](turing-complete-vector-fields.md)
- [Smooth vector fields](../../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/smooth-vector-field.md)

## Proof depends on

None.

## Expansion

The definition treats the Euler evolution as an infinite-dimensional dynamical system on $\mathfrak X^\infty_{\mathrm{vol}}(M)$, by analogy with Turing complete vector fields; when the equations are Turing complete, the undecidability of the halting problem makes it undecidable whether the solution with an explicit initial datum enters an explicit open set.

## Sources

- Robert Cardona, Eva Miranda and Daniel Peralta-Salas, "Turing universality of the incompressible Euler equations and a conjecture of Moore", *International Mathematics Research Notices* 2022(22), 2022, pp. 18092–18109, <https://doi.org/10.1093/imrn/rnab233>; read as arXiv:2104.04356v1, <https://arxiv.org/abs/2104.04356v1>: the Euler equations and the space $\mathfrak X^\infty_{\mathrm{vol}}(M)$ in Section 1, and Definition 5.1 in Section 5 of that version.
