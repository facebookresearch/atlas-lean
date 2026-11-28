# Flux coupling relations and their feasibility tests

**Setting.** Use the network $(S, \mathrm{Irr})$, its steady-state flux cone $C$, the coupling relations $\xrightarrow{=0}$, $\xleftrightarrow{=0}$, $\backsim$ and the reversibility classes of [flux coupling relations](flux-coupling-relations-and-kernel-test-for-full-coupling.md): $i \xrightarrow{=0} j$ means $v_i = 0 \Rightarrow v_j = 0$ for all $v \in C$. Assume blocked reactions have been deleted and every reversible reaction whose flux has constant sign on $C$ has been made irreversible (flipping its column if needed), so that $\mathrm{Irev}$ is the set of irreversible reactions, every reaction of $\mathrm{Prev}$ (pseudo-irreversible) takes both signs on $C$, and $\mathrm{Frev}$ is the set of fully reversible reactions.

**Proposition (feasibility characterization).** Consider the linear systems, each including $Sv = 0$:

- (P1) $v_k \ge 0$ for $k\in\mathrm{Irr}$, $v_i = 1$, $v_j = 0$;
- (P2) $v_k \ge 0$ for $k\in\mathrm{Irr}$, $v_i = 0$, $v_j = 1$;
- (P3) $v_k \ge 0$ for $k\in\mathrm{Irr}$, $v_i = 0$, $v_j = -1$;
- (P4) $v_i = 0$, $v_j = 1$ (no sign constraints).

Then:

- for $i,j \in \mathrm{Irev}$, $j \xrightarrow{=0} i$ iff (P1) is infeasible and $i \xrightarrow{=0} j$ iff (P2) is infeasible, so both infeasible means $i \xleftrightarrow{=0} j$;
- for $i \in\mathrm{Irev}$ and $j\in\mathrm{Prev}$, $i \xrightarrow{=0} j$ iff (P2) and (P3) are both infeasible;
- for $i,j$ both in $\mathrm{Prev}$ or both in $\mathrm{Frev}$, $i \backsim j$ iff (P4) is infeasible.

The source writes the relations in the opposite direction, $i \to j$ for $v_i \ne 0 \Rightarrow v_j \ne 0$, which is $j \xrightarrow{=0} i$ here.

## Expansion

For $i\in\mathrm{Irev}$, $j \xrightarrow{=0} i$ fails iff some $v \in C$ has $v_i \ne 0$ and $v_j = 0$; then $v_i > 0$ and, $C$ being a cone, $v/v_i$ solves (P1), and conversely a solution of (P1) is such a witness. The same scaling argument handles (P2) and, for $j \in\mathrm{Prev}$ whose flux takes both signs, (P2) together with (P3). For two reactions in $\mathrm{Prev}$ or in $\mathrm{Frev}$, full coupling is equivalent to the implication $v_i = 0 \Rightarrow v_j = 0$ on the whole null space of $S$ (irreversibility constraints dropped), and a violating null-space vector can be scaled to $v_j = 1$, which is (P4). Deciding coupling by feasibility rather than by solving two optimization problems per pair, together with the restrictions on which reversibility types can be coupled ([linear programming tests and reduction rules](linear-programming-tests-and-reduction-rules-for-flux-coupling.md)), is what makes the feasibility-based method faster on genome-scale networks; distinguishing full from partial coupling among $\mathrm{Irev}$ pairs still requires a ratio test.

## Depends on

- [Flux coupling relations and the kernel test for full coupling](flux-coupling-relations-and-kernel-test-for-full-coupling.md)

## Proof depends on

- [Linear programming tests and reduction rules for flux coupling](linear-programming-tests-and-reduction-rules-for-flux-coupling.md)

## Sources

- L. David, S.-A. Marashi, A. Larhlimi, B. Mieth, A. Bockmayr, "FFCA: a feasibility-based method for flux coupling analysis of metabolic networks", BMC Bioinformatics 12 (2011) 236, Background (flux coupling relations, reversibility types) and Results (systems P1–P4), <https://doi.org/10.1186/1471-2105-12-236>, PMCID PMC3144024.
- A. P. Burgard, E. V. Nikolaev, C. H. Schilling, C. D. Maranas, "Flux coupling analysis of genome-scale metabolic network reconstructions", Genome Research 14 (2004) 301–312, <https://doi.org/10.1101/gr.1926504>.
- A. Larhlimi, A. Bockmayr, "A new constraint-based description of the steady-state flux cone of metabolic networks", Discrete Applied Mathematics 157 (2009) 2257–2266, <https://doi.org/10.1016/j.dam.2008.06.039>.
