# E-class analyses

An *e-class analysis* on [e-graphs](e-graphs.md) consists of a domain $D$ with a join operation $\vee$ making $(D, \vee)$ a join-semilattice, and three functions: $\mathrm{make}(n) \in D$ for a new e-node $n$, computed from the data of its children; $\mathrm{join}(d_{c_1}, d_{c_2}) = d_{c_1} \vee d_{c_2}$ for e-classes being merged; and an optional $\mathrm{modify}(c)$ that changes an e-class according to its data, typically by adding an e-node, and is idempotent when nothing else changes. Each e-class $c$ carries a value $d_c \in D$. The *analysis invariant* states that for every e-class $c$,

$$d_c = \bigvee_{n \in c} \mathrm{make}(n) \quad\text{and}\quad \mathrm{modify}(c) = c,$$

so in particular $d_c \ge \mathrm{make}(n)$ for every $n \in c$. The invariant is the target of the analysis. [Rebuilding](rebuilding-restores-the-congruence-invariant.md) is extended to work towards it alongside the [congruence invariant](congruence-and-hashcons-invariants-of-e-graphs.md): $\mathrm{add}$ sets the data of a new singleton e-class to $\mathrm{make}(n)$ and applies $\mathrm{modify}$, $\mathrm{merge}$ joins the data of the merged e-classes, and repairing an e-class applies $\mathrm{modify}$ to it and recomputes the data of its parents, joining in $\mathrm{make}$ of each parent e-node and putting a parent e-class back on the worklist when its data change. These assumptions on $D$, $\mathrm{make}$ and $\mathrm{modify}$ do not guarantee that the invariant can be reached: for the e-class $C = \{a, f(C)\}$, the domain $\mathbb{N}$ with join $\max$, identity $\mathrm{modify}$, $\mathrm{make}(a) = 0$ and $\mathrm{make}(f(C)) = d_C + 1$, the invariant would require $d_C = \max(0, d_C + 1)$, which has no solution, and the updates of $d_C$ never stop.

## Depends on

- [Rebuilding restores the congruence invariant](rebuilding-restores-the-congruence-invariant.md)
- [E-graphs](e-graphs.md)
- [Congruence and hashcons invariants of e-graphs](congruence-and-hashcons-invariants-of-e-graphs.md)

## Sources

- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock and P. Panchekha, "egg: Fast and extensible equality saturation", *Proceedings of the ACM on Programming Languages* 5(POPL), Article 23, 2021, doi:10.1145/3434304, author copy arXiv:2004.03082v3 <https://arxiv.org/abs/2004.03082>, Section 4.1: the interface make, join and modify, the semilattice requirement, the analysis invariant, and Section 4.1.1 with Figure 9 on maintaining it during rebuilding, where a parent whose data change is put back on the worklist; Theorem 3.1 concerns rebuilding without analyses. The example without a fixed point is written out here.
