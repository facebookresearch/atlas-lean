# Existence for the Sturm–Liouville Dirichlet problem on the closed unit interval

Let $V$
and $f$ be continuous real functions on $[0, 1]$ with $V \ge 0$. Then there is a function
$u \colon \mathbb{R} \to \mathbb{R}$ that is $C^2$ on $[0, 1]$, satisfies
$-u''(x) + V(x)\,u(x) = f(x)$ for every $x \in [0, 1]$, with the second derivative taken within
$[0, 1]$, and has $u(0) = u(1) = 0$.

The proof is by the shooting method: let $u_0$ solve the equation with $u_0(0) = u_0'(0) = 0$,
and let $w$ solve the homogeneous equation $-w'' + V w = 0$ with $w(0) = 0$ and $w'(0) = 1$. An
energy argument using $V \ge 0$ shows $w(1) \ne 0$, and $u = u_0 + a w$ with
$a = -u_0(1)/w(1)$ is the required solution.

## Sources

- `SpectralTheory.sturm_liouville_existence` in the v1 formalization, whose formalization is left unproved there; the proof here is original.
