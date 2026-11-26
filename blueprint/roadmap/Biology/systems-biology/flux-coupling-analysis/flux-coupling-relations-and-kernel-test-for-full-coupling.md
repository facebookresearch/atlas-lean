# Flux coupling relations and the kernel test for full coupling

A metabolic network is a pair $(S, \mathrm{Irr})$ with stoichiometric matrix $S \in \mathbb{R}^{m \times n}$ ($m$ internal metabolites, $n$ reactions) and a set $\mathrm{Irr} \subseteq \{1, \dots, n\}$ of irreversible reactions. Its **steady-state flux cone** is

$$C = \{ v \in \mathbb{R}^n : S v = 0,\ v_i \ge 0 \text{ for all } i \in \mathrm{Irr} \}.$$

A reaction $i$ is **blocked** if $v_i = 0$ for all $v \in C$. For unblocked reactions $i, j$:
- $i \xrightarrow{=0} j$ (**directional coupling**) if $v_i = 0 \Rightarrow v_j = 0$ for all $v \in C$;
- $i \xleftrightarrow{=0} j$ (**partial coupling**) if $v_i = 0 \Leftrightarrow v_j = 0$ for all $v \in C$;
- $i \backsim j$ (**full coupling**) if there is $\lambda \ne 0$ with $v_j = \lambda v_i$ for all $v \in C$;
- $i \mapsto j$ (**uncoupling witness**) if some $v \in C$ has $v_i = 0$ and $v_j \ne 0$.

Full coupling implies partial coupling, which is the conjunction of the two directional couplings; directional coupling is transitive. A reversible reaction $i$ is **fully reversible** if some $v \in C$ has $v_i \ne 0$ and $v_k = 0$ for all $k \in \mathrm{Irr}$, and **pseudo-irreversible** otherwise; together with the irreversible-and-unblocked and the blocked reactions these classes partition $\{1, \dots, n\}$.

**Lemma (kernel test).** Suppose no reaction of $(S, \mathrm{Irr})$ is blocked. Then $i \backsim j$ if and only if there is $\lambda \ne 0$ with $v_i = \lambda v_j$ for every $v \in \ker S$.

Thus, after blocked reactions are removed, all fully coupled pairs can be read off a basis of the null space of $S$ (proportional rows of a kernel basis matrix), without any linear programming.

## Expansion

The "if" direction is immediate since $C \subseteq \ker S$. For "only if", take $v \in \ker S$ with $v_i \ne \lambda v_j$ and let $L = \{ l \in \mathrm{Irr} : v_l < 0 \}$. Because every reaction is unblocked, for each $l \in L$ there is $g^{(l)} \in C$ with $g^{(l)}_l = 1$. Then $w = v - \sum_{l \in L} v_l\, g^{(l)}$ lies in $\ker S$ and has $w_l \ge 0$ on $\mathrm{Irr}$, so $w \in C$; since $g^{(l)} \in C$ satisfies the proportionality, $w_i - \lambda w_j = v_i - \lambda v_j \ne 0$, contradicting $i \backsim j$. The unblocked hypothesis is essential: a blocked reaction would make the cone strictly smaller than the irreversibility-respecting part of the kernel in ways the kernel cannot see.

## Sources

- A. Larhlimi, L. David, J. Selbig and A. Bockmayr, "F2C2: a fast tool for the computation of flux coupling in genome-scale metabolic networks", BMC Bioinformatics 13 (2012) 57, Eq. (1), Definitions 1–3 and Lemma 1, <https://doi.org/10.1186/1471-2105-13-57>, PMCID PMC3515416.
- A. P. Burgard, E. V. Nikolaev, C. H. Schilling and C. D. Maranas, "Flux coupling analysis of genome-scale metabolic network reconstructions", Genome Research 14 (2004) 301–312, <https://doi.org/10.1101/gr.1926504>.
