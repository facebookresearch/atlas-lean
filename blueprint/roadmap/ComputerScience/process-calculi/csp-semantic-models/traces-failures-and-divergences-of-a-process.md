# Traces, failures and divergences of a process

Let $C$ be a labelled transition system with labels in $\Sigma^{\checkmark} \cup \{\tau\}$, where $\Sigma^{\checkmark} = \Sigma \cup \{\checkmark\}$ and $\checkmark$ is the termination signal, such as the [operational semantics of CSP](csp-operational-semantics.md). Observations are taken in $\Sigma^{*\checkmark} = \Sigma^* \cup \{ s ^\frown \langle \checkmark \rangle \mid s \in \Sigma^* \}$: nothing after $\checkmark$ is recorded. For $s \in \Sigma^{*\checkmark}$ write $P \xRightarrow{s} Q$ if some sequence $s'$ of labels with $s' \setminus \tau = s$ leads from $P$ to $Q$. Let $P^0$ be the set of labels of the transitions of $P$.

- $\mathrm{traces}(P) = \{ s \in \Sigma^{*\checkmark} \mid \exists Q .\ P \xRightarrow{s} Q \}$.
- $P$ *can diverge* if there are $P_0 = P, P_1, P_2, \dots$ with $P_n \xrightarrow{\tau} P_{n+1}$ for every $n$, and $\mathrm{divergences}(P) = \{ s ^\frown t \mid s \in \Sigma^*,\ t \in \Sigma^{*\checkmark},\ \exists Q .\ P \xRightarrow{s} Q \text{ and } Q \text{ can diverge} \}$.
- For $B \subseteq \Sigma^{\checkmark}$, $P$ *refuses* $B$ if either $P$ is stable (it has no $\tau$ and no $\checkmark$ transition) and $B \cap P^0 = \emptyset$, or $P \xrightarrow{\checkmark} Q$ for some $Q$ and $B \subseteq \Sigma$.
- $\mathrm{failures}(P) = \{ (s, X) \mid s \in \Sigma^{*\checkmark},\ \exists Q .\ P \xRightarrow{s} Q \text{ and } Q \text{ refuses } X \} \cup \{ (s ^\frown \langle \checkmark \rangle, X) \mid s \in \Sigma^*,\ X \subseteq \Sigma^{\checkmark},\ \exists Q .\ P \xRightarrow{s ^\frown \langle \checkmark \rangle} Q \}$.
- $\mathrm{traces}_\bot(P) = \mathrm{traces}(P) \cup \mathrm{divergences}(P)$ and $\mathrm{failures}_\bot(P) = \mathrm{failures}(P) \cup \{ (s, X) \mid s \in \mathrm{divergences}(P),\ X \subseteq \Sigma^{\checkmark} \}$.

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 7.4.1 ("Extracting failures and divergences"): the relations $\xrightarrow{s}$ and $\xRightarrow{s}$, the definitions of $\mathrm{traces}$, divergence, with the remark that nothing a process does after $\checkmark$ is recorded, $\mathrm{divergences}$, the refusal relation, $\mathrm{failures}$, $\mathrm{traces}_\bot$ and $\mathrm{failures}_\bot$.
