# Unique steady states of Michaelis-Menten realizations of substrate hypergraph cycles

**Setting.** A *substrate hypergraph* $\mathcal H=(\mathcal S,\mathcal R)$ has a finite set $\mathcal S$ of substrates and a finite set $\mathcal R$ of composite reactions $\rho:t_\rho\to h_\rho$, where the tail $t_\rho$ and head $h_\rho$ are nonnegative integer combinations of substrates. $\mathcal H$ is a **cycle** if it is strongly connected and every substrate is produced by exactly one reaction and consumed by exactly one reaction, each time with coefficient one; equivalently, its dual (reactions as nodes, substrates as edges from producer to consumer) is a strongly connected ordinary directed graph. An *enzyme assignment* $\sigma:\mathcal R\to\{0,1,\dots,m\}$ attaches to each reaction an enzyme $E_{\sigma(\rho)}$, possibly shared with other reactions, or none ($\sigma(\rho)=0$). The **Henri-Michaelis-Menten (HMM) realization** replaces each reaction by the mass-action module
$$E_{\sigma(\rho)}+t_\rho\ \underset{k_\rho^-}{\overset{k_\rho^+}{\rightleftarrows}}\ C_\rho\ \xrightarrow{\ k_\rho\ }\ E_{\sigma(\rho)}+h_\rho$$
with an intermediate complex $C_\rho$ and positive rate constants (enzyme-free reactions omit $E$). A stoichiometric compatibility class is *positive* if it contains a strictly positive point; its state vector $u$ collects substrates, free enzymes and intermediates, with mass-action vector field $f$.

**Theorem 1.1 (main theorem).** Let $\mathcal H$ be a finite substrate hypergraph cycle. For every enzyme assignment and all positive rate constants:
1. each positive stoichiometric compatibility class contains exactly one positive steady state and no steady state on the boundary of the nonnegative orthant;
2. every trajectory starting in a positive class is strictly positive for $t>0$ and its $\omega$-limit set lies in the open orthant, so the realization is persistent;
3. the realization is injective: $f(u^{(1)})\ne f(u^{(2)})$ for distinct strictly positive states in the same class.

**Theorem 1.2 (global convergence without enzyme sharing).** If each enzyme catalyzes at most one reaction (enzyme-free reactions allowed), then for all positive rate constants every trajectory in a positive class converges to the unique positive steady state of that class.

**Theorem 8.3 and Theorem 8.5 (weighted cycles).** Both conclusions extend to *weighted cycles*, where each substrate is still produced and consumed by exactly one reaction but with arbitrary positive integer coefficients, and (Proposition 8.4, Proposition 8.6) to modules with longer chains of intermediates or direct reactions.

## Expansion

Because the dual is a strongly connected graph, the only steady-state current is a multiple of the all-ones vector (Proposition 2.2): at steady state every composite reaction carries the same flux. Each directed cycle of the dual and each enzyme give a conservation law, and a class is positive exactly when all these totals are positive (Proposition 3.3). Uniqueness and injectivity follow by comparing two putative steady states reaction by reaction along the cycle; existence comes from a fixed-point argument on the common flux, and boundary steady states are excluded because a vanishing substrate forces the whole cycle's flux to vanish. With distinct enzymes, each module is a monotone futile-cycle-like unit, and a convergence theorem for monotone systems written in reaction coordinates gives global attraction.

## Sources

- B. Joshi, T. D. Nguyen, "Substrate hypergraph cycles: unique steady states and persistence for every enzyme assignment; oscillations enabled by enzyme sharing", arXiv preprint (2026), Theorem 1.1, Theorem 1.2, Proposition 2.2, Proposition 3.3, Theorem 8.3, Proposition 8.4, Theorem 8.5, Proposition 8.6, <https://doi.org/10.48550/arXiv.2611.02523>.
