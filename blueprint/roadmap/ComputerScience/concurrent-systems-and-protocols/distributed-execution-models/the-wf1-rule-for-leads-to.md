# The WF1 rule for leads-to

Let $P$ and $Q$ be state predicates, $\mathcal{N}$ and $A$ actions, and $f$ a state function (typically the tuple of all variables). Write $[\mathcal{N}]_f$ for $\mathcal{N} \vee f' = f$, $\langle A \rangle_f$ for $A \wedge f' \ne f$, and $\mathrm{WF}_f(A)$ for weak fairness of $\langle A \rangle_f$. If

1. $P \wedge [\mathcal{N}]_f \Rightarrow (P' \vee Q')$,
2. $P \wedge \langle \mathcal{N} \wedge A \rangle_f \Rightarrow Q'$, and
3. $P \Rightarrow \mathrm{Enabled}\, \langle A \rangle_f$,

then $\Box[\mathcal{N}]_f \wedge \mathrm{WF}_f(A) \Rightarrow (P \leadsto Q)$: in every behavior satisfying $\Box[\mathcal{N}]_f$ and $\mathrm{WF}_f(A)$, whenever $P$ holds, $Q$ holds then or later.

## Expansion

This page becomes ready once these prerequisites are stated:

- Weak and strong fairness (statement prerequisite)

## Sources

- L. Lamport, "The temporal logic of actions", *ACM Transactions on Programming Languages and Systems* 16(3):872–923, 1994, Section 5.6, Figure 5 (rule WF1) and its justification, <https://lamport.azurewebsites.net/pubs/lamport-actions.pdf>
- L. Lamport, *Specifying Systems*, Addison-Wesley, 2002
