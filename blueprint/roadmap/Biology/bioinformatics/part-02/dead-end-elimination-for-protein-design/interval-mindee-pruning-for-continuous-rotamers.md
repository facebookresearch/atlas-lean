# Interval MinDEE pruning for continuous rotamers

**Setting.** A design system has residue positions $i = 1, \dots, n$, each with a finite set of rotamers. A **continuous rotamer** $i_r$ is a voxel of side-chain dihedral angles around a modal conformation. A rotamer assignment $a$ picks one rotamer per position, and its energy $E(a)$ is the pairwise-decomposable energy minimized over all dihedrals inside the chosen voxels. For each continuous rotamer and each pair, precompute lower bounds $E^-(i_r)$ and $E^-(i_r, j_s)$, the minimum of the internal and pairwise energy over the voxel(s) when no other side chain is present, and set

$$E^-(a) = E_{\mathrm{t}} + \sum_i E^-(i_{a_i}) + \sum_{i<j} E^-(i_{a_i}, j_{a_j}) \le E(a),$$

where $E_{\mathrm{t}}$ is the template energy. Let $a^\ast$ minimize $E^-$ and let $g$ be the minimized global minimum energy conformation (minGMEC), which minimizes $E$.

**Interval.** Define $I := E(g) - E^-(a^\ast) \ge 0$.

**Proposition (iMinDEE criterion).** If, for rotamers $i_r \ne i_t$ at position $i$, and for some $I' \ge I$,

$$E^-(i_r) + \sum_{j \ne i} \min_s E^-(i_r, j_s) - I' \;>\; E^-(i_t) + \sum_{j \ne i} \max_s E^-(i_t, j_s),$$

then $i_r$ is not part of the minGMEC and can be pruned.

**Greedy estimation of minimization.** Since $I$ depends on the unknown $g$, guess $I_0 \ge 0$, prune with $I' = I_0$, and let A* enumerate the surviving assignments in increasing order of $E^-$, minimizing each, with $b$ the best minimized assignment found. Put $I_1 := E(b) - E^-(a^\ast)$. If $I_1 \le I_0$ then $I \le I_0$, so no pruning step removed $g$ and $b$ is the minGMEC; otherwise $I \le I_1$ and one more pruning and search with $I' = I_1$ is guaranteed to find the minGMEC.

## Expansion

Suppose $g$ uses $i_r$, and let $g'$ be $g$ with $i_r$ replaced by $i_t$. Only terms involving position $i$ change, so

$$E^-(g') - E^-(g) = \Bigl[E^-(i_t) + \sum_j E^-(i_t, j_{g_j})\Bigr] - \Bigl[E^-(i_r) + \sum_j E^-(i_r, j_{g_j})\Bigr] < -I' \le -I,$$

using the max bound on the first bracket and the min bound on the second. Hence $E^-(g') < E^-(g) - I \le E(g) - I = E^-(a^\ast)$, contradicting the minimality of $E^-(a^\ast)$. The GEM check uses $E(b) \ge E(g)$, so $I_1 \ge I$ always. The earlier MinDEE criterion needed upper bounds on voxel energies to absorb every possible minimization-induced change; those upper bounds can be loose by tens of kcal/mol for packed aromatic pairs, whereas a single interval term keeps pruning close to rigid-rotamer DEE. Rigid DEE is the special case in which every voxel is a point, so $E^- = E$, $I = 0$, and the criterion becomes the classical Desmet condition.

## Sources

- P. Gainza, K. E. Roberts, B. R. Donald, "Protein design using continuous rotamers", PLoS Computational Biology 8 (2012) e1002335, Results, sections "Rigid DEE criterion", "Greedy Estimation of Minimization (GEM)" and "Interval MinDEE", Equations (6)–(8), Propositions 1 and 2, <https://doi.org/10.1371/journal.pcbi.1002335> (PMC3257257).
