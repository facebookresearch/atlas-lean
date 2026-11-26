# Flux coupling relations and their feasibility tests

**Setting.** A metabolic network has stoichiometric matrix $S \in \mathbb{R}^{m\times n}$ (internal metabolites by reactions) and a set $\mathrm{Irr}$ of irreversible reactions. The **steady-state flux cone** is
$$C = \{v \in \mathbb{R}^n : Sv = 0,\ v_k \ge 0\ \text{for } k \in \mathrm{Irr}\},$$
with lineality space $\{v : Sv = 0,\ v_k = 0 \text{ for } k\in\mathrm{Irr}\}$. Reaction $r$ is **blocked** if $v_r = 0$ for all $v \in C$. Unblocked reactions are partitioned into $\mathrm{Irev}$ (sign-constant on $C$; after flipping columns, $v_r \ge 0$ on $C$), $\mathrm{Prev}$ (both signs occur on $C$ but $v_r = 0$ on the lineality space) and $\mathrm{Frev}$ (nonzero somewhere on the lineality space). For unblocked $i,j$:
- $i \to j$ (**directionally coupled**) if $v_i \ne 0 \Rightarrow v_j \ne 0$ for all $v \in C$;
- $i \leftrightarrow j$ (**partially coupled**) if $i\to j$ and $j \to i$;
- $i \Leftrightarrow j$ (**fully coupled**) if moreover $v_j/v_i$ is a constant on $\{v \in C: v_i\ne 0\}$;
- **uncoupled** if neither $i\to j$ nor $j\to i$.

**Reversibility-type restrictions.** Two unblocked reactions can be coupled only in the cases (i) $i,j \in \mathrm{Irev}$ (any relation), (ii) $i \in \mathrm{Irev}$, $j \in \mathrm{Prev}$ (only $j \to i$), (iii) $i,j \in \mathrm{Prev}$ (only $i\Leftrightarrow j$), (iv) $i,j\in\mathrm{Frev}$ (only $i \Leftrightarrow j$).

**Proposition (feasibility characterization).** Consider the linear systems, each including $Sv = 0$:
- (P1) $v_k \ge 0$ for $k\in\mathrm{Irr}$, $v_i = 1$, $v_j = 0$;
- (P2) $v_k \ge 0$ for $k\in\mathrm{Irr}$, $v_i = 0$, $v_j = 1$;
- (P3) $v_k \ge 0$ for $k\in\mathrm{Irr}$, $v_i = 0$, $v_j = -1$;
- (P4) $v_i = 0$, $v_j = 1$ (no sign constraints).

Then: for $i,j \in \mathrm{Irev}$, $i \to j$ iff (P1) is infeasible and $j \to i$ iff (P2) is infeasible, so both infeasible means partial (possibly full) coupling; for $i \in\mathrm{Irev}$, $j\in\mathrm{Prev}$, $j \to i$ iff (P2) and (P3) are both infeasible; for $i,j$ both in $\mathrm{Prev}$ or both in $\mathrm{Frev}$ (blocked reactions removed), $i \Leftrightarrow j$ iff (P4) is infeasible.

## Expansion

For $i\in\mathrm{Irev}$, $i \to j$ fails iff some $v \in C$ has $v_i \ne 0$ and $v_j = 0$; then $v_i > 0$ and, $C$ being a cone, $v/v_i$ solves (P1), and conversely a solution of (P1) is such a witness. The same scaling argument handles (P2) and, for $j \in\mathrm{Prev}$ whose flux takes both signs, (P2) together with (P3). For two reactions in $\mathrm{Prev}$ or in $\mathrm{Frev}$, full coupling is equivalent to the implication $v_i = 0 \Rightarrow v_j = 0$ on the whole null space of $S$ (irreversibility constraints dropped), and a violating null-space vector can be scaled to $v_j = 1$, which is (P4). Deciding coupling by feasibility rather than by solving two optimization problems per pair, together with the reversibility-type restrictions, is what makes the feasibility-based method faster on genome-scale networks; distinguishing full from partial coupling among $\mathrm{Irev}$ pairs still requires a ratio test.

## Sources

- L. David, S.-A. Marashi, A. Larhlimi, B. Mieth, A. Bockmayr, "FFCA: a feasibility-based method for flux coupling analysis of metabolic networks", BMC Bioinformatics 12 (2011) 236, Background (flux coupling relations, reversibility-type prunings) and Results (systems P1–P4), <https://doi.org/10.1186/1471-2105-12-236>, PMCID PMC3144024.
- A. P. Burgard, E. V. Nikolaev, C. H. Schilling, C. D. Maranas, "Flux coupling analysis of genome-scale metabolic network reconstructions", Genome Research 14 (2004) 301–312, <https://doi.org/10.1101/gr.1926504>.
- A. Larhlimi, A. Bockmayr, "A new constraint-based description of the steady-state flux cone of metabolic networks", Discrete Applied Mathematics 157 (2009) 2257–2266.
