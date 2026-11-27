# Treewidth-parameterized Boltzmann sampling of multi-target RNA designs

Let $R_1, \dots, R_k$ be secondary structures on positions $1,\dots,n$. A sequence $S \in \{A,C,G,U\}^n$ is a **valid design** if every pair $(i,j) \in \bigcup_\ell R_\ell$ is canonical ($\{S_i, S_j\} \in \{AU, GC, GU\}$). Each feature $F_\ell(S)$ (the energy of $S$ folded into $R_\ell$, and $F_0$ the GC content) is a sum of local contributions $f$, each depending on a set $\mathrm{dep}(f)$ of positions (for the stacking model, the four positions $\{i, i+1, j-1, j\}$ of each stack in some $R_\ell$). For weights $\pi = (\pi_0,\dots,\pi_k) > 0$ the target distribution is

$$\mathbb{P}(S \mid \pi) = \frac{1}{Z_\pi}\prod_{\ell=0}^{k} \pi_\ell^{-F_\ell(S)} .$$

Let $G_F$ be the **dependency hypergraph** on $\{1,\dots,n\}$ with hyperedges $\mathrm{dep}(f)$. A **tree decomposition** $(T,\chi)$ assigns bags $\chi(v) \subseteq \{1,\dots,n\}$ to nodes of a tree so that every position is in some bag, the bags containing a position form a subtree, and every hyperedge lies in some bag; its **treewidth** is $\max_v |\chi(v)| - 1$.

**Theorem.** Given a tree decomposition of $G_F$ of width $w$, the partition function $Z_\pi$ can be computed, and $t$ sequences sampled exactly from $\mathbb{P}(\cdot \mid \pi)$, in

$$O\big(n\,k\,4^{w+1} + t\,n\,k\big)$$

time (precomputation improvable to $O(n k\, 2^{w+1} 2^{c})$, where $c \le w+1$ bounds the number of base-pair-connected components in a bag). Sampling is therefore fixed-parameter tractable in the treewidth.

Weights achieving prescribed expected energies $\mathbb{E}(F_\ell \mid \pi) = E_\ell^\star$ exist on a convex optimization landscape ($\mathbb{E}(F_\ell \mid \pi)$ decreases in $\pi_\ell$), giving multidimensional Boltzmann sampling with a final rejection step to energies within tolerance.

## Depends on

- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)

## Expansion

The algorithm is cluster-tree elimination: each contribution is assigned to one bag containing its dependencies, and messages from child to parent bags tabulate, for each nucleotide assignment of their separator, the partition function of the subtree; multiplying the messages at the root gives $Z_\pi$, and stochastic backtracking reverses the computation to draw sequences. Message tables have $4^{|\text{separator}|}$ entries and each step ranges over one extra position, which yields the $4^{w+1}$ factor; the number of contributions and bags is $O(nk)$. Realistic loop-based energies can be encoded exactly but raise the treewidth, so a structure-specific affine fit of Turner energies to stacking energies is used to target realistic free energies.

## Sources

- S. Hammer, W. Wang, S. Will and Y. Ponty, "Fixed-parameter tractable sampling for RNA design with multiple target structures", BMC Bioinformatics 20 (2019), Definition 1, Algorithms 1–2, Theorem 1 and multidimensional Boltzmann sampling, <https://doi.org/10.1186/s12859-019-2784-7>, PMCID: PMC6482512.
