# Dynamic information-flow monitoring with no sensitive upgrades

Let labels form a lattice with order $\sqsubseteq$, join $\sqcup$ and bottom $\bot$. The language $\lambda^{\mathrm{info}}$ has variables, constants, abstractions, application, reference
allocation $\mathbf{ref}\ e$, dereference $!e$, assignment $e := e$ and labelling $\langle k\rangle e$. Under *universal labelling*, every runtime value carries a label, and the
big-step judgement $\sigma, \theta, e \Downarrow_{pc} \sigma', v$ evaluates $e$ in store $\sigma$ and environment $\theta$ under a program-counter label $pc$: results computed under $pc$ get a label above
$pc$, a branch on a value labelled $k$ evaluates under $pc \sqcup k$, and dereferencing an address labelled $k$ joins $k$ into the result. An assignment $e_1 := e_2$ with $e_1$
evaluating to an address $a$ labelled $k$ (so $pc \sqsubseteq k$) is allowed only if $k \sqsubseteq \mathrm{label}(\sigma(a))$, and stores the new value joined with $k$; otherwise
evaluation stops with an error. This *no-sensitive-upgrade* check forbids writing to a public cell under a secret program counter, which would otherwise leak through
implicit flows.

Two values are *$H$-equivalent*, $v_1 \sim_H v_2$, if they are equal, if both have label at least $H$, or if they are closures with the same code and $H$-equivalent
environments; stores are *$H$-compatible*, $\sigma_1 \approx_H \sigma_2$, if they agree up to $\sim_H$ on their common addresses.

## Depends on

- [Security levels, policies and low equivalence](../information-flow/security-levels-policies-and-low-equivalence.md)

## Sources

- T. H. Austin and C. Flanagan, "Efficient purely-dynamic information flow analysis", *Proceedings of the ACM SIGPLAN Fourth Workshop on Programming Languages and Analysis for Security (PLAS 2009)*, pp. 113–124, copy at <https://users.soe.ucsc.edu/~cormac/papers/plas09.pdf>: Section 2, Figure 1 (the language), Section 3, Figure 2 (universal labelling rules, U-Assign with the no-sensitive-upgrade check) and Section 3.1 ($H$-equivalence and $H$-compatibility).
