# Billiard tables and billiard flows

A billiard table is a bounded planar domain with finitely piecewise smooth boundary, and its billiard flow moves a point particle at unit speed along straight lines with elastic reflection at the boundary; a trajectory is periodic when it returns to its initial position and velocity.

A *billiard table* is a bounded planar domain $B \subset \mathbb{R}^2$ whose boundary $\partial B$ is finitely piecewise smooth, that is, smooth except at finitely many singular points. The *billiard flow* $\varphi_t$ on the phase space $\{(q, v) \in B \times \mathbb{R}^2 : |v| = 1\}$ follows the free motion $q(t) = q_0 + t v_0$ until the first collision with $\partial B$, where the velocity is reflected by

$$
v^+ = v^- - 2\langle v^-, n \rangle n ,
$$

with $n$ the inward unit normal at the point of impact, so that the angle of incidence equals the angle of reflection; it is defined on the trajectories that avoid the singular points of $\partial B$. A trajectory is *periodic* if it returns to its initial position with its initial velocity. A point or direction is *computable* if a Turing machine outputs rational approximations of it to within $2^{-n}$ on input $n$.

## Depends on

None.

## Proof depends on

None.

## Sources

- E. Miranda and I. Ramos, "Two-dimensional billiards are Turing complete", Proceedings of the National Academy of Sciences of the United States of America 123 (2026), no. 37, e2614500123, https://doi.org/10.1073/pnas.2614500123; read in arXiv:2512.19156v5 (Sections 2.1 and 2.3 of arXiv:2512.19156v5, billiards and computable points).
