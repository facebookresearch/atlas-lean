# The Feller domain of the neutral Wright–Fisher generator

For the neutral Wright–Fisher diffusion without mutation ($\alpha = \theta = 0$), the generator $A$ of its Feller semigroup on $C[0, 1]$ has domain

$$D(A) = \Bigl\{ f \in C[0, 1] \cap C^2(0, 1) : x(1 - x) f''(x) \to 0 \text{ as } x \to 0^+ \text{ and as } x \to 1^- \Bigr\},$$

and $A f = \frac{1}{2} x(1 - x) f''$. The boundaries $0$ and $1$ are absorbing exit boundaries, which forces $A f = 0$ there.

The proof uses only the necessity half of the Hille–Yosida theorem, [that generators of contraction semigroups are dissipative](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/necessity-half-of-hille-yosida-generators-of-con.md), with its resolvent facts. The sufficiency half is not used.

## Proof depends on

- [Polynomials form a core for the neutral WF semigroup](polynomials-form-a-core-for-the-neutral-wf-semig.md)
- [Generator of the Wright–Fisher diffusion on polynomials](tendsto-wf-semigroup-sub-div.md)
- [Necessity half of Hille-Yosida: generators of contraction semigroups are dissipative](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/necessity-half-of-hille-yosida-generators-of-con.md)

## Expansion

1. The inclusion of the polynomial core, from [the polynomial core](polynomials-form-a-core-for-the-neutral-wf-semig.md) and [the generator on polynomials](tendsto-wf-semigroup-sub-div.md), and the closure of $A$ on the stated domain.
2. The reverse inclusion from the resolvent equation.
3. A nonmembership test: $T(x) = -2\bigl(x \log x + (1 - x) \log(1 - x)\bigr)$ has $x(1 - x) T'' = -2$, which does not tend to $0$. So $T \notin D(A)$; otherwise $P_t T = T - t$, contradicting $T \ge 0$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658> (one-dimensional diffusion generators).
- W. Feller, The parabolic differential equations and the associated semi-groups of transformations, *Ann. of Math.* 55 (1952), 468–519, <https://doi.org/10.2307/1969644> (generator domains and boundary conditions).
