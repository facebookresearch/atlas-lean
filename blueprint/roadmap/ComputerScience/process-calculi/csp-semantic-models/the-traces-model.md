# The traces model of CSP

Let $\Sigma^{*\checkmark} = \Sigma^* \cup \{ s ^\frown \langle \checkmark \rangle \mid s \in \Sigma^* \}$ be the set of finite traces over the alphabet $\Sigma$ that may end with the termination signal $\checkmark$. The *traces model* $\mathcal{T}$ is the set of nonempty, prefix-closed subsets of $\Sigma^{*\checkmark}$. A process $P$ of a labelled transition system is represented in $\mathcal{T}$ by $\mathrm{traces}(P)$, and *trace refinement* is reverse containment: $P \sqsubseteq_T Q$ if and only if $\mathrm{traces}(Q) \subseteq \mathrm{traces}(P)$. Two processes are trace equivalent when each trace-refines the other.

## Depends on

- [Traces, failures and divergences of a process](traces-failures-and-divergences-of-a-process.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 1.3 ("The traces model and traces refinement") and Section 8.2 ("The traces model"), whose first paragraph defines $\mathcal{T}$ and the refinement order as reverse containment.
