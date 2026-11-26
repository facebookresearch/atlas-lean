# RAF sets and the maxRAF algorithm

**Catalytic reaction system.** A catalytic reaction system (CRS) is a tuple $\mathcal Q = (X, \mathcal R, C, F)$ where $X$ is a finite set of molecule types, $\mathcal R$ a finite set of reactions, each reaction $r$ having a set of reactants $\rho(r) \subseteq X$ and products $\pi(r) \subseteq X$, $C \subseteq X \times \mathcal R$ the catalysis relation ($(x, r) \in C$ means $x$ catalyses $r$), and $F \subseteq X$ the food set.

**Closure.** For $\mathcal R' \subseteq \mathcal R$, the closure $\mathrm{cl}_{\mathcal R'}(F)$ is the smallest set $W \supseteq F$ such that $\rho(r) \subseteq W$ implies $\pi(r) \subseteq W$ for every $r \in \mathcal R'$; it is obtained by repeatedly firing reactions of $\mathcal R'$ whose reactants are present.

**Definition.** A non-empty $\mathcal R' \subseteq \mathcal R$ is

- *food-generated* ($F$-generated) if $\rho(r) \subseteq \mathrm{cl}_{\mathcal R'}(F)$ for every $r \in \mathcal R'$;
- *reflexively autocatalytic* if every $r \in \mathcal R'$ is catalysed by some $x \in \mathrm{cl}_{\mathcal R'}(F)$, that is, $(x, r) \in C$;
- a *RAF set* if it is both.

**Theorem.** (i) The union of two RAF sets is a RAF set. Hence, if $\mathcal Q$ contains a RAF, it contains a unique maximal RAF (the maxRAF), the union of all RAFs. (ii) The maxRAF is found by the following iteration: set $\mathcal R_0 = \mathcal R$ and

$$\mathcal R_{i+1} = \big\{ r \in \mathcal R_i : \rho(r) \subseteq \mathrm{cl}_{\mathcal R_i}(F) \text{ and } (x, r) \in C \text{ for some } x \in \mathrm{cl}_{\mathcal R_i}(F) \big\};$$

the sequence is decreasing and stabilises at the maxRAF (or at $\emptyset$ if there is no RAF) in at most $|\mathcal R|$ rounds, with worst-case running time $O(|\mathcal R|^2 \log |\mathcal R|)$. (iii) A RAF is *irreducible* (irrRAF) if no proper subset is a RAF; there can be exponentially many irrRAFs inside a maxRAF, and finding a smallest one is NP-complete, but irrRAFs can be sampled by deleting a random reaction from a RAF and re-running the reduction until no deletion leaves a RAF.

## Expansion

Closure is monotone in the reaction set, so for RAFs $\mathcal R_1, \mathcal R_2$ every reactant and catalyst witnessed in $\mathrm{cl}_{\mathcal R_k}(F)$ is still present in $\mathrm{cl}_{\mathcal R_1 \cup \mathcal R_2}(F)$, proving (i). For (ii), every RAF $\mathcal R' \subseteq \mathcal R_i$ survives the step $i \to i+1$ by the same monotonicity, so each $\mathcal R_i$ contains the maxRAF; at the fixed point $\mathcal R_{i+1} = \mathcal R_i$ the set itself satisfies both RAF conditions. Each round removes at least one reaction or stops, and each closure can be computed in $O(|\mathcal R|\log|\mathcal R|)$ time with sorted reactant lists. In the *E. coli* cytosolic network (with cofactors as catalysts and spontaneous reactions allowed), the maxRAF contains almost all reactions, and removing individual catalysts or reactions shows strong interdependence between cofactor biosynthesis modules.

## Sources

- F. L. Sousa, W. Hordijk, M. Steel, W. F. Martin, "Autocatalytic sets in E. coli metabolism", Journal of Systems Chemistry 6 (2015) 4, Background and Experimental (RAF definitions, RAF algorithm with $O(|R|^2\log|R|)$ worst-case time, unique maxRAF, irrRAF sampling algorithm), <https://doi.org/10.1186/s13322-015-0009-7> (PMC4429071).
- W. Hordijk, M. Steel, "Detecting autocatalytic, self-sustaining sets in chemical reaction systems", Journal of Theoretical Biology 227 (2004) 451–461, <https://doi.org/10.1016/j.jtbi.2003.11.020>.
