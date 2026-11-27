# Algebraic criterion for degenerate reaction networks

**Setting.** A mass-action network $G$ with $s$ species, stoichiometric subspace $S$ of dimension $r$ and rate vector $\kappa$ defines $\dot x = f(\kappa, x)$. $G$ is *consistent* if some $\kappa$ gives a positive steady state. A steady state $x^*$ is *degenerate* if $\operatorname{im}\bigl(\mathrm{Jac}_f(\kappa^*, x^*)|_S\bigr) \ne S$. $G$ is a *degenerate network* if it is consistent and every positive steady state (for every $\kappa$) is degenerate. A *zero-one network* is one in which every reactant complex has coefficients in $\{0,1\}$; a species is *trivial* if in every reaction it is absent or appears on both sides.

**Theorem.**
1. Let $A(\lambda)$ be the partial transformed Jacobian matrix, i.e. the Jacobian of $f$ rewritten in the positive parameters $\lambda$ of a parametrisation of all positive steady states over all rate constants. Then $G$ is degenerate if and only if $\det\bigl(A(\lambda)[I,I]\bigr)$ is the zero polynomial for every $I \subseteq \{1, \dots, s\}$ with $|I| = r$.
2. One-dimensional zero-one networks are never degenerate.
3. For every degenerate two-dimensional zero-one network with three species, after removing trivial species, each polynomial of the steady-state system augmented with conservation laws consists of exactly two monomials in $x$ (the steady-state system is binomial).

## Expansion

At a positive steady state, nondegeneracy means the Jacobian restricted to $S$ is invertible, which is detected by the $r \times r$ principal minors of the Jacobian. Writing steady states through a positive parametrisation turns this into polynomial identities in $\lambda$, and a polynomial vanishes for all positive arguments only if it is identically zero; checking each principal minor gives an exact algorithm. Exhaustive enumeration with this test produced all degenerate two-dimensional zero-one networks with up to three species, all of which have binomial steady-state ideals.

## Sources

- X. Tang, Y. Wang, J. Zhang, "Degeneracy of Two-Dimensional Zero-One Reaction Networks with Up to Three Species", *Journal of Systems Science and Complexity* 39(5) (2026), 1881–1900, degeneracy criterion (Section 3) and main theorem on binomial steady-state systems (Section 6), <https://doi.org/10.1007/s11424-026-5441-z> (preprint arXiv:2507.09272).
