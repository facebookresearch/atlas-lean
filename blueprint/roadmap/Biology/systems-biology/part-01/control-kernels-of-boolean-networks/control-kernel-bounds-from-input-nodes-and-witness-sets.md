# Control kernel bounds from input nodes and witness sets

A synchronous Boolean network on $n$ nodes updates $x_i(t+1) = f_i(x_1(t), \dots, x_n(t))$ with $f_i : \{0,1\}^n \to \{0,1\}$; every trajectory ends in an **attractor** (fixed point or cycle), and its **basin** is the set of states converging to it. **Pinning** a node $j$ to a value $b$ replaces $f_j$ by the constant $b$, giving a network on the remaining $n - 1$ free nodes.

**Definition (control kernel).** For an attractor $A$, a control kernel (CK) is a set of nodes of minimal size whose pinning to their values in $A$ makes the basin of $A$ the whole configuration space. A fixed point always has a CK (pin everything); a cycle may have none, since only nodes constant on the cycle can be pinned.

**Definition (input node).** A node is an input node if its update rule is the identity, $f_p(x) = x_p$.

**Proposition 1.** Every CK contains all input nodes.

**Definition (distinguishing nodes, witness set).** For a family $\mathcal A = \{A_1, \dots, A_r\} \subseteq \{0,1\}^n$ of distinct vectors, $W_i \subseteq \{1, \dots, n\}$ is a **witness set** for $A_i$ if every $A_j \ne A_i$ differs from $A_i$ in some coordinate of $W_i$. For fixed-point attractors, a set of distinguishing nodes of $A$ is a witness set for $A$ within the original attractors (nodes varying along a cycle count as differing from every constant value).

**Proposition 2.** Every CK of $A$ contains a set of distinguishing nodes of $A$ with respect to the network's original attractors.

**Bounds.** Let $m$ be the number of input nodes and, after pinning them to their values in $A$, let $w^{(1)}$ be a minimal witness set for $A$ against the remaining original attractors and $w^{(i)}$, $i \ge 2$, minimal witness sets against the attractors newly created by successive rounds of pinning. Then

$$m + |w^{(1)}| \;\le\; |\mathrm{CK}| \;\le\; m + |w^{(1)}| + \sum_{i \ge 2} |w^{(i)}| .$$

## Expansion

Unpinned input nodes keep both values viable forever, so no other pinning can select between the attractors they index (Proposition 1). Pinning node $j$ to $b$ deletes the $2^{n-1}$ states with $x_j = \bar b$; an attractor is removed exactly when it uses such a state, so removing every competitor of $A$ requires a witness set (Proposition 2). Pinning can also create attractors (a state agreeing with its image except in the pinned coordinate becomes a fixed point), whence the upper bound; pinning an input node never creates one. A random-transition heuristic predicts about one new fixed point per round, so the first-order approximation $m + |w^{(1)}|$ dominates. Since revealing one bit roughly halves the candidate attractors, average minimal witness sets tend to scale like $\log_2 r$, matching the empirical $\langle|\mathrm{CK}|\rangle \approx \log_2 r$ across curated cell-regulatory networks, though exceptions to $\log_2 r$ as an upper bound for witness sets exist (finite projective planes).

## Sources

- E. Borriello, B. C. Daniels, "The basis of easy controllability in Boolean networks", Nature Communications 12 (2021) 5227, Eq. 1–2, Definitions 1–4 and Propositions 1–2, <https://doi.org/10.1038/s41467-021-25533-3>, PMCID PMC8410781.
