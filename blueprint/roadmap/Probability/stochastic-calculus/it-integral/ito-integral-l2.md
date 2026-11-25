# Itô integral as an element of $L^2$

Let $P$ be a measure, $F$ a filtration, $B, H$ real processes and $t \ge 0$. The Itô integral $\int_0^t H\, dB$ as
an element of $L^2(P)$ is defined as follows. If $H$ is [Itô-approximable](is-ito-approximable.md) on $[0, t]$,
take a chosen approximating sequence of elementary integrands $H^{(n)}$ and their
[elementary Itô integrals](ito-integral.md) $\int_0^t H^{(n)}\, dB$, each viewed in $L^2(P)$ [through the
square-integrable class, or $0$](to-l2.md): the integral is their limit in $L^2(P)$ when it exists,
and otherwise an unspecified element of $L^2(P)$ fixed by a choice. If $H$ is not Itô-approximable,
it is $0$.

For an adapted pre-Brownian integrator $B$ whose increments are independent of the past, the limit
exists and is the same along every approximating sequence ([well-definedness](tendsto-to-l2-ito-integral.md)).

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.
