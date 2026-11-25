# Well-posedness of the Turing reaction–diffusion system

Local well-posedness of the two-species reaction–diffusion system $u_t = d_u \Delta u + f_1(u, v)$,
$v_t = d_v \Delta v + f_2(u, v)$ in the space $C(K, \mathbb{R}^2)$ of continuous fields on a compact
space $K$ with the sup norm. The diffusion enters through a C₀ semigroup $H$ on $C(K, \mathbb{R})$,
intended to be the Neumann heat semigroup on $C(\overline{\Omega})$ for a bounded domain $\Omega$,
and the diffusion coefficients satisfy $d_u, d_v \ge 0$. For $C^1$ kinetics, mild solutions exist on
a time interval uniform over a ball of initial data, are unique, depend Lipschitz-continuously on
the data and restart as a semiflow. The Schnakenberg kinetics qualify; the Gierer–Meinhardt
kinetics, singular at $v = 0$, do not.

## Species coordinates

- [Concentration field of one species](species-proj.md)
- [Field of one species alone](species-emb.md)
- [The species projection reads off one coordinate](species-proj-apply.md)
- [A single-species field at a point](species-emb-apply.md)
- [Projecting a single-species field](species-proj-species-emb.md)

## The diffusion semigroup

- [Diagonal diffusion operators diag(H(d_u t), H(d_v t))](diffusion-semigroup.md)
- [Each species evolves by the scalar operator at its own time](diffusion-semigroup-apply-apply.md)
- [The diffusion operators of a C₀ semigroup form a C₀ semigroup](is-c0-semigroup-diffusion-semigroup.md)
- [Single-species eigenfunctions of the diffusion operators](diffusion-semigroup-apply-species-emb.md)

## Local well-posedness for C¹ kinetics

- [C¹ maps on a finite-dimensional space are Lipschitz on closed balls](exists-lipschitz-on-with-closed-ball-of.md)
- [Local well-posedness of the Turing system for C¹ kinetics](local-flow.md)
- [Mild solutions of the Turing system with C¹ kinetics are unique](is-mild-solution-unique.md)
- [Restarting a mild solution of the Turing system at a later time](is-mild-solution-restart.md)

## Homogeneous steady states

- [If H fixes constants, the diffusion operators fix constant fields](diffusion-semigroup-apply-const.md)
- [If H fixes constants, homogeneous steady states are mild solutions](is-mild-solution-const.md)

## Schnakenberg and Gierer–Meinhardt kinetics

- [The Schnakenberg kinetics are smooth](cont-diff-schnakenberg.md)
- [Local well-posedness of the Schnakenberg–Turing system](schnakenberg-local-flow.md)
- [The Gierer–Meinhardt kinetics are not Lipschitz on the unit ball](not-lipschitz-on-with-gierer-meinhardt.md)
