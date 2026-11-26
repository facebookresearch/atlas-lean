# The stable failures model of CSP

With $\Sigma^{*\checkmark} = \Sigma^* \cup \{ s ^\frown \langle \checkmark \rangle \mid s \in \Sigma^* \}$ and $\Sigma^{\checkmark} = \Sigma \cup \{\checkmark\}$, the *stable failures model* $\mathcal{F}$ consists of the pairs $(T, F)$ with $T \subseteq \Sigma^{*\checkmark}$ and $F \subseteq \Sigma^{*\checkmark} \times \mathcal{P}(\Sigma^{\checkmark})$ that satisfy:

- T1: $T$ is nonempty and prefix closed;
- T2: $(s, X) \in F$ implies $s \in T$;
- F2: $(s, X) \in F$ and $Y \subseteq X$ imply $(s, Y) \in F$;
- F3: $(s, X) \in F$ and $s ^\frown \langle a \rangle \notin T$ for every $a \in Y$ imply $(s, X \cup Y) \in F$;
- F4: $s ^\frown \langle \checkmark \rangle \in T$ implies $(s, \Sigma) \in F$;
- T3: $s ^\frown \langle \checkmark \rangle \in T$ implies $(s ^\frown \langle \checkmark \rangle, X) \in F$ for every $X \subseteq \Sigma^{\checkmark}$.

A process $P$ of a labelled transition system is represented in $\mathcal{F}$ by $(\mathrm{traces}(P), \mathrm{failures}(P))$, and the refinement order is $(T, F) \sqsubseteq_F (T', F')$ if and only if $T \supseteq T'$ and $F \supseteq F'$.

## Depends on

- [Traces, failures and divergences of a process](traces-failures-and-divergences-of-a-process.md)
- [The traces model of CSP](the-traces-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.4 ("The stable failures model"): the healthiness conditions T1, T2, F2–F4 and T3 and the refinement order $\sqsubseteq_F$; conditions F2–F4 are those of Section 8.3.1 with $T$ in place of $\mathrm{traces}_\bot(P)$.
