# Global asymptotic stability of saturated linear systems is undecidable

No algorithm decides, given a rational square matrix A, whether the saturated linear system x⁺ = sat(Ax), with saturation applied componentwise, is globally asymptotically stable.

**Theorem (Blondel, Bournez, Koiran and Tsitsiklis).** For $v \in \mathbb R^n$ let $\mathrm{sat}(v)$ be the componentwise saturation $\mathrm{sat}(v)_i = \min(\max(v_i, -1), 1)$. The following problem is undecidable: given $n \ge 1$ and a matrix $A \in \mathbb Q^{n \times n}$, is the saturated linear system

$$
x_{k+1} = \mathrm{sat}(A x_k), \qquad x_k \in \mathbb R^n,
$$

[globally asymptotically stable](global-asymptotic-stability-of-discrete-time-maps.md)?

The dimension $n$ is part of the input. The map $x \mapsto \mathrm{sat}(Ax)$ is continuous, piecewise affine and fixes the origin.

## Depends on

- [Global asymptotic stability of a discrete-time system](global-asymptotic-stability-of-discrete-time-maps.md)

## Proof depends on

None.

## Expansion

The proof reduces the Turing machine immortality problem, whether a given Turing machine has a configuration from which it never halts, which Hooper proved undecidable. It first simulates any Turing machine by a saturated linear system with a strong notion of simulation, then shows that it is undecidable whether a given continuous piecewise affine system has a trajectory contained in a given hyperplane, and finally reduces this problem to stability, global convergence, mortality and nilpotence of saturated linear systems. The source proves all four properties undecidable in the same theorem. Through the identity $\mathrm{sat}(z) = \mathrm{ReLU}(z + 1) - \mathrm{ReLU}(z - 1) - 1$ the result also reduces to stability of linear plants with ReLU neural-network feedback.

## Sources

- Vincent D. Blondel, Olivier Bournez, Pascal Koiran and John N. Tsitsiklis, "The stability of saturated linear dynamical systems is undecidable", *Journal of Computer and System Sciences* 62(3), 2001, pp. 442–462, <https://doi.org/10.1006/jcss.2000.1737>; read in the authors' copy at <http://web.mit.edu/people/jnt/Papers/J085-01-vb-satur.pdf>: Theorem 2.1 (main statement, for saturated linear functions $x \mapsto \mathrm{sat}(Ax)$ with $A \in \mathbb Q^{n \times n}$) and its proof in Sections 3 to 6, which uses Hooper's undecidability of Turing machine immortality (Theorem 3.2 there).
- Milan Korda, "Stability and performance verification of dynamical systems controlled by neural networks: algorithms and complexity", *IEEE Control Systems Letters* 6, 2022, pp. 3265–3270, <https://doi.org/10.1109/LCSYS.2022.3181806>; read as arXiv:2102.02273v5, <https://arxiv.org/abs/2102.02273v5>: the statement as recalled (as Theorem 2.1 of the first source) in the proof of Theorem 3 of that version, with the saturation function and rational matrix as above.
