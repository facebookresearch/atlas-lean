# The integral of φ(rest of configuration) · f(one offspring) factorizes

Let the offspring numbers $\xi_{n,i}$ and the contact targets $U_j$ form a
[final-size epidemic model](is-final-size-epidemic.md) on a probability space $(\Omega, P)$, in the
population $\{0, \dots, N-1\}$, with offspring law $\nu$, a probability measure on $\mathbb{N}$. For
every index $p_0 = (n_0, i_0)$, every function $\varphi$ from [configurations](config.md) to
$\mathbb{R}$, measurable for the product $\sigma$-algebra, and every
$f : \mathbb{N} \to \mathbb{R}$, writing $Y(\omega) = w^{p_0}(\omega)$ for the
[configuration at $\omega$ without $p_0$](config-without.md) and $X = \xi_{n_0,i_0}$,
$\int \varphi(Y) f(X) \, dP = \int \varphi(Y) \, dP \int f(X) \, dP$. The integral of a
non-integrable function is $0$ by convention, and the identity holds as stated without any
integrability assumption.
