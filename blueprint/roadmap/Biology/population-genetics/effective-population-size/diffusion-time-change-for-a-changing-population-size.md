# Deterministic time change for a changing population size

For the neutral Wright–Fisher diffusion in a population whose size is $\nu(t)$ times a reference size, with $\nu$ positive and measurable and $1/\nu$ locally integrable, the generator at time $t$ is $L_t = \nu(t)^{-1}L_0$ with $L_0f = \frac12x(1-x)f''$. Then the process is the reference-size diffusion run on the deterministic clock $A(t) = \int_0^t\nu(s)^{-1}\,ds$: if $Y$ is the neutral Wright–Fisher diffusion with generator $L_0$, then $X_t = Y_{A(t)}$ has the time-inhomogeneous generator $L_t$, and its path law is the image of that of $Y$ under the time change. This follows from the chain rule: $f(Y_{A(t)})$ has drift $A'(t)L_0f(Y_{A(t)}) = \nu(t)^{-1}L_0f(X_t)$. It is the diffusion counterpart of the variable-size coalescent, in which a pair of lineages coalesces at rate $1/\nu(t)$ (Bhaskar and Song 2014, Sec. 2).

## Expansion

1. The clock $A$, its continuity and strict monotonicity, and its inverse.
2. The time-changed process and its martingale problem with generator $L_t$, by the chain rule for $f(Y_{A(t)})$.
3. Uniqueness of the time-inhomogeneous martingale problem, hence identification of the path law.
4. The coalescent counterpart: the [cumulative coalescence intensity](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/cum-rate.md) of the variable-size coalescent.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
