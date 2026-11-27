# Dynamic information-flow monitoring with no sensitive upgrades

Let labels form a lattice with order $\sqsubseteq$, join $\sqcup$ and bottom $\bot$. The language $\lambda^{\mathrm{info}}$ has variables, constants, abstractions, application, reference
allocation $\mathbf{ref}\ e$, dereference $!e$, assignment $e := e$ and labelling $\langle k\rangle e$. Under *universal labelling*, every runtime value carries a label, and the
big-step judgement $\sigma, \theta, e \Downarrow_{pc} \sigma', v$ evaluates $e$ in store $\sigma$ and environment $\theta$ under a program-counter label $pc$: results computed under $pc$ get a label above
$pc$, applying a closure labelled $k$ evaluates its body under $pc \sqcup k$, allocation $\mathbf{ref}\ e$ (rule U-Ref) evaluates $e$ to $v$ with store $\sigma'$ and returns a
fresh address $a \notin \mathrm{dom}(\sigma')$ labelled $pc$, written $a^{pc}$, with store $\sigma'[a := v]$, and dereferencing an address labelled $k$ joins $k$ into the result. An assignment $e_1 := e_2$ first evaluates
$\sigma, \theta, e_1 \Downarrow_{pc} \sigma_1, a^k$ to an address $a$ labelled $k$ (so $pc \sqsubseteq k$), then $\sigma_1, \theta, e_2 \Downarrow_{pc} \sigma_2, v$; it is allowed only if $k \sqsubseteq \mathrm{label}(\sigma_2(a))$, the
label of the cell in the store after both operands, and then returns $v$ with store $\sigma_2[a := v \sqcup k]$, the value $v$ with $k$ joined into its label; otherwise evaluation
stops with an error. This *no-sensitive-upgrade* check forbids writing to a public cell under a secret program counter, which would otherwise leak through
implicit flows.

Two values are *$H$-equivalent*, $v_1 \sim_H v_2$, if they are equal, if both have label at least $H$, or if they are closures $(\lambda x.e, \theta_1)^k$ and $(\lambda x.e, \theta_2)^k$ with the same
code, the same label and $\theta_1 \sim_H \theta_2$, where two environments are $H$-equivalent when they have the same domain and are pointwise $H$-equivalent; stores are *$H$-compatible*, $\sigma_1 \approx_H \sigma_2$, if they agree up to $\sim_H$ on their common addresses.

## Depends on

- [Security levels, policies and low equivalence](../information-flow/security-levels-policies-and-low-equivalence.md)

## Sources

- T. H. Austin and C. Flanagan, "Efficient purely-dynamic information flow analysis", *Proceedings of the ACM SIGPLAN Fourth Workshop on Programming Languages and Analysis for Security (PLAS 2009)*, pp. 113–124, copy at <https://users.soe.ucsc.edu/~cormac/papers/plas09.pdf>: Section 2, Figure 1 (the language), Section 3, Figure 2 (universal labelling rules, U-Assign with the no-sensitive-upgrade check on $\sigma_2$) and Section 3.1 ($H$-equivalence, whose closure clause requires the same label, $H$-equivalence of substitutions and $H$-compatibility).
