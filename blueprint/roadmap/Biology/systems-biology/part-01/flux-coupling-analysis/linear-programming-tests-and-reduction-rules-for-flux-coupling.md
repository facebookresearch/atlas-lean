# Linear programming tests and reduction rules for flux coupling

Use the flux cone $C$, the coupling relations $\xrightarrow{=0}, \xleftrightarrow{=0}, \backsim, \mapsto$ and the reversibility classes (fully reversible $\mathrm{Frev}$, pseudo-irreversible $\mathrm{Prev}$, irreversible $\mathrm{Irev}$, blocked $\mathrm{Blk}$) of [flux coupling relations](flux-coupling-relations-and-kernel-test-for-full-coupling.md), and assume blocked reactions have been deleted and every reversible reaction whose flux has constant sign on $C$ has been made irreversible (flipping its column if needed), so that $\mathrm{Irev}$ is the set of irreversible reactions and every reaction of $\mathrm{Prev}$ takes both signs on $C$.

**Where coupling can occur.** For unblocked $i \ne j$ a coupling is possible only in three situations.

1. *Both reversible of the same type* ($i, j \in \mathrm{Prev}$ or $i, j \in \mathrm{Frev}$): then $i \xrightarrow{=0} j$, $i \xleftrightarrow{=0} j$ and $i \backsim j$ are equivalent and depend only on $S$. With $v^*$ optimal for $\max\{ v_j : S v = 0,\ v_i = 0,\ 0 \le v_j \le 1 \}$, one has $i \xrightarrow{=0} j$ iff $v^*_j = 0$.
2. *$i \in \mathrm{Irev}$, $j \in \mathrm{Prev}$*: only $i \xrightarrow{=0} j$ can hold, and it holds iff both $\max$ and $\min$ of $v_j$ over $\{ v \in C : v_i = 0,\ |v_j| \le 1 \}$ are $0$.
3. *Both irreversible* ($i, j \in \mathrm{Irev}$): let

    $$L_{ij} = \min\{ v_i : v \in C,\ v_j = 1 \}, \qquad L_{ji} = \min\{ v_j : v \in C,\ v_i = 1 \}.$$

    Then $i \xrightarrow{=0} j$ iff $L_{ij} \ne 0$, $j \xrightarrow{=0} i$ iff $L_{ji} \ne 0$, and $i \backsim j$ iff both are nonzero and $L_{ij} L_{ji} = 1$.

**Reduction and inference rules.**

- *Dead-end metabolite:* if metabolite $k$ occurs in a single reaction, or only in irreversible reactions that all produce (or all consume) it, those reactions are blocked; deleting such rows and the blocked columns preserves all couplings among the remaining reactions.
- *Trivial full coupling:* if metabolite $k$ occurs in exactly two reactions $i, j$, they are blocked or fully coupled; fully coupled columns $k, l$ with $v_l = \lambda v_k$ ($\lambda > 0$) can be merged into the single column $S_{\ast k} + \lambda S_{\ast l}$, made irreversible if $l$ is irreversible, without changing any other coupling.
- *Trivial directional coupling:* if metabolite $k$ occurs only in irreversible reactions and has a unique producer $i$ (resp. a unique consumer $j$), then $i \xrightarrow{=0} j'$ for every consumer $j'$ (resp. $j \xrightarrow{=0} i'$ for every producer $i'$).
- *Feasibility rule:* any $v \in C$ certifies $i \mapsto j$ for all $i$ with $v_i = 0$ and $j$ with $v_j \ne 0$.
- *Removing a fully reversible reaction* does not change the couplings among the non-fully-reversible reactions; up to $\dim \ker S_{\ast \mathrm{Rev}}$ such deletions can be made.

## Depends on

- [Flux coupling relations and the kernel test for full coupling](flux-coupling-relations-and-kernel-test-for-full-coupling.md)

## Expansion

For case 3, $L_{ij} > 0$ says that any flux with $v_j = 1$, hence by scaling any flux with $v_j > 0$, has $v_i > 0$, which is the contrapositive of $i \xrightarrow{=0} j$ for irreversible reactions; full coupling means the ratio $v_i / v_j$ is constant, which forces $\min v_i / v_j = L_{ij}$ and $\min v_j / v_i = L_{ji}$ to be reciprocal. Replacing the possibly unbounded problems of the classical Flux Coupling Finder by these bounded minimizations yields an optimal flux vector at every call, which the feasibility rule turns into many uncoupling certificates for free. Merging coupled columns and deleting dead ends and blocked reactions shrinks genome-scale networks substantially before any LP is solved; with the kernel test for full coupling and transitivity of directional coupling, most pairs are decided without an LP.

## Sources

- A. Larhlimi, L. David, J. Selbig and A. Bockmayr, "F2C2: a fast tool for the computation of flux coupling in genome-scale metabolic networks", BMC Bioinformatics 13 (2012) 57, Eqs. (2)–(5), Observations 1–7 and Lemma 2, <https://doi.org/10.1186/1471-2105-13-57>, PMCID PMC3515416.
