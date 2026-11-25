# Maximum principle for compact self-adjoint operators

Let $T$ be a compact self-adjoint
operator on a Hilbert space $H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then one of the
following two alternatives holds.

Either there are $N \in \mathbb{N}$ (possibly $N = 0$, as for $T = 0$), nonzero real numbers
$s_0, \dots, s_{N-1}$ and an orthonormal family $u_0, \dots, u_{N-1}$ in $H$ such that
$T u_i = s_i u_i$ for every $i < N$, $|s_0| \ge |s_1| \ge \dots \ge |s_{N-1}|$, for every $i < N$
every unit vector $x \in H$ orthogonal to $u_0, \dots, u_{i-1}$ satisfies
$|\langle T x, x \rangle| \le |s_i|$ while $|\langle T u_i, u_i \rangle| = |s_i|$, and $T x = 0$
for every $x \in H$ orthogonal to all of $u_0, \dots, u_{N-1}$.

Or there are nonzero real numbers $s_0, s_1, s_2, \dots$ and an orthonormal sequence
$u_0, u_1, u_2, \dots$ in $H$ such that $T u_n = s_n u_n$ for every $n$, the sequence $|s_n|$ is
nonincreasing and tends to $0$ as $n \to \infty$, for every $n$ every unit vector $x \in H$
orthogonal to $u_0, \dots, u_{n-1}$ satisfies $|\langle T x, x \rangle| \le |s_n|$ while
$|\langle T u_n, u_n \rangle| = |s_n|$, and $T x = 0$ for every $x \in H$ orthogonal to every
$u_n$.
