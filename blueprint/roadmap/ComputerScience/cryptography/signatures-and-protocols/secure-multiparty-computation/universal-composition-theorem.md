# Universal composition theorem

Use [UC emulation](uc-emulation.md). For protocols $\rho$ and $\phi$ with $\phi$ a sub-protocol of $\rho$, and a protocol $\pi$, write $\rho^{\phi \to \pi}$ for $\rho$ with every call to $\phi$
replaced by a call to $\pi$; for an ideal functionality $\mathcal{F}$, $\rho^{\mathcal{F} \to \pi}$ abbreviates the replacement of the ideal protocol for $\mathcal{F}$.

**Theorem (universal composition).** Let $\rho$, $\phi$ and $\pi$ be protocols such that $\phi$ is a sub-protocol of $\rho$ and $\pi$ UC-emulates $\phi$. Then $\rho^{\phi \to \pi}$ UC-emulates $\rho$.
In particular, if $\pi$ UC-realizes $\mathcal{F}$ then $\rho^{\mathcal{F} \to \pi}$ UC-emulates $\rho$, and if $\rho$ UC-realizes $\mathcal{G}$ then so does $\rho^{\mathcal{F} \to \pi}$.

This is the qualitative statement in Canetti's simplified presentation; in the general framework the theorem carries further conditions on how the protocols use their subroutines.

## Depends on

- [UC emulation](uc-emulation.md)

## Expansion

This page becomes ready once:

- The compliance and subroutine-respecting conditions of the general framework, under which the theorem holds for arbitrary protocols (statement prerequisite; not yet stated)

## Sources

- R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC summer school, Boston University, 2025, <https://www.bu.edu/riscs/files/2025/08/Canetti.pdf>: the universal composition theorem and its quantitative version.
