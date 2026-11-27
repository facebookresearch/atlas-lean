# The failures-divergences model of CSP

With $\Sigma^{*\checkmark} = \Sigma^* \cup \{ s ^\frown \langle \checkmark \rangle \mid s \in \Sigma^* \}$ and $\Sigma^{\checkmark} = \Sigma \cup \{\checkmark\}$, the *failures-divergences model* $\mathcal{N}$ consists of the pairs $P = (F, D)$ with $F \subseteq \Sigma^{*\checkmark} \times \mathcal{P}(\Sigma^{\checkmark})$ and $D \subseteq \Sigma^{*\checkmark}$ that satisfy, where $\mathrm{traces}_\bot(P) = \{ t \mid (t, X) \in F \text{ for some } X \}$, $s, t$ range over $\Sigma^{*\checkmark}$ and $X, Y$ over subsets of $\Sigma^{\checkmark}$:

- F1: $\mathrm{traces}_\bot(P)$ is nonempty and prefix closed;
- F2: $(s, X) \in F$ and $Y \subseteq X$ imply $(s, Y) \in F$;
- F3: $(s, X) \in F$ and $s ^\frown \langle a \rangle \notin \mathrm{traces}_\bot(P)$ for every $a \in Y$ imply $(s, X \cup Y) \in F$;
- F4: $s ^\frown \langle \checkmark \rangle \in \mathrm{traces}_\bot(P)$ implies $(s, \Sigma) \in F$;
- D1: $s \in D \cap \Sigma^*$ and $t \in \Sigma^{*\checkmark}$ imply $s ^\frown t \in D$;
- D2: $s \in D$ implies $(s, X) \in F$;
- D3: $s ^\frown \langle \checkmark \rangle \in D$ implies $s \in D$.

A process $P$ of a labelled transition system is represented in $\mathcal{N}$ by $(\mathrm{failures}_\bot(P), \mathrm{divergences}(P))$. Failures-divergences refinement is reverse containment, $(F, D) \sqsubseteq_{FD} (F', D')$ if and only if $F \supseteq F'$ and $D \supseteq D'$, and its least element is $\bot_{\mathcal{N}} = (\Sigma^{*\checkmark} \times \mathcal{P}(\Sigma^{\checkmark}), \Sigma^{*\checkmark})$.

## Depends on

- [Traces, failures and divergences of a process](traces-failures-and-divergences-of-a-process.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.3.1 ("Building the model"): the healthiness conditions F1–F4 and D1–D3, the refinement order $\sqsubseteq_{FD}$ and the element $\bot_{\mathcal{N}}$.
