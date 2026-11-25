# Trotter-Kurtz: chain semigroups converge to a limit semigroup

Let $E$ be a compact metric space, $(T(t))_{t\ge0}$ a Feller semigroup on $C(E)$ with generator $A$, and $D\subseteq D(A)$ a core for $A$: the closure of $A|_D$ is $A$. Let $T_N$ be positive linear contractions on $C(E)$ and $a_N>0$ with $a_N\to\infty$. If

$$\sup_{x\in E}\bigl|a_N(T_Nf-f)(x)-Af(x)\bigr|\longrightarrow0\qquad\text{for every }f\in D,$$

then for every $f\in C(E)$ and every $t_0<\infty$,

$$\sup_{0\le t\le t_0}\bigl\|T_N^{\lfloor a_Nt\rfloor}f-T(t)f\bigr\|_\infty\longrightarrow0.$$

The neutral Wright–Fisher chain is an instance: [$\lfloor tM\rfloor$ generations of the chain with $M$ gene copies converge to the diffusion semigroup](../../../Biology/population-genetics/diffusion-theory/wright-fisher-semigroup-and-moment-duality/tendsto-wf-step-pow-floor.md).

## Proof depends on

- [Trotter–Kato approximation theorem](../../../Analysis/operator-theory/trotter-kato-approximation-theorem.md)

## Expansion

A proof page must establish: the comparison of $T_N^{\lfloor a_Nt\rfloor}$ with the semigroup $e^{ta_N(T_N-I)}$, whose difference applied to $f\in D$ is bounded by a multiple of $a_N^{-1/2}\|a_N(T_N-I)f\|_\infty$ (a Poisson-versus-deterministic count of steps); convergence $e^{ta_N(T_N-I)}f\to T(t)f$, locally uniformly in $t$, from generator convergence on a core (Trotter–Kato); extension from $D$ to $C(E)$ by density of $D$ and the uniform contraction bounds; and a test with random-walk chains on $\frac1N\mathbb Z$ folded onto a compact interval by reflection, converging to the reflected heat semigroup.

## Sources

- H. F. Trotter, *Approximation of semi-groups of operators*, Pacific Journal of Mathematics 8 (1958), 887–919, <https://msp.org/pjm/1958/8-4/pjm-v8-n4-p20-s.pdf>, Theorem 5.3 (statement and proof).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Chapter 1, Section 6 (approximation theorems).
