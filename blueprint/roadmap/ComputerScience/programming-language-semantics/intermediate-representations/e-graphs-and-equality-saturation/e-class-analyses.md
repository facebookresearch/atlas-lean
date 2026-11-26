# E-class analyses

An *e-class analysis* on [e-graphs](e-graphs.md) consists of a domain $D$ with a join operation $\vee$ making $(D, \vee)$ a join-semilattice, and three functions: $\mathrm{make}(n) \in D$ for a new e-node $n$, computed from the data of its children; $\mathrm{join}(d_{c_1}, d_{c_2}) = d_{c_1} \vee d_{c_2}$ for e-classes being merged; and an optional $\mathrm{modify}(c)$ that changes an e-class according to its data, typically by adding an e-node, and is idempotent when nothing else changes. Each e-class $c$ carries a value $d_c \in D$. The *analysis invariant* states that for every e-class $c$,

$$d_c = \bigvee_{n \in c} \mathrm{make}(n) \quad\text{and}\quad \mathrm{modify}(c) = c,$$

so in particular $d_c \ge \mathrm{make}(n)$ for every $n \in c$. Rebuilding is extended to restore it alongside the [congruence invariant](congruence-and-hashcons-invariants-of-e-graphs.md).

## Depends on

- [E-graphs](e-graphs.md)
- [Congruence and hashcons invariants of e-graphs](congruence-and-hashcons-invariants-of-e-graphs.md)

## Sources

- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock and P. Panchekha, "egg: Fast and extensible equality saturation", arXiv:2004.03082, <https://arxiv.org/abs/2004.03082> (also *Proceedings of the ACM on Programming Languages* 5(POPL):23, 2021), Section 4.1: the interface make, join and modify, the semilattice requirement, the analysis invariant, and Section 4.1.1 on maintaining it during rebuilding.
