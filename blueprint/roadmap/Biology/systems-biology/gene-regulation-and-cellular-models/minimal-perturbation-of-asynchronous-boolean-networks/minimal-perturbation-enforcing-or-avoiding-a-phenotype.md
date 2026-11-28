# Minimal perturbation enforcing or avoiding a phenotype

Let a gene regulatory network on $n$ genes have Boolean regulation functions, updated **asynchronously**: at each step one regulation function acts, so a global state can have several successors. Its state graph $G = (V,E)$ has the $|V| = 2^n$ global states as nodes and an edge $(a,b)$ whenever some regulation function acting in $a$ yields $b$.

A **perturbation** $P$ is a set of operations on genes, each either an *activation* (gene fixed at level $1$) or a *repression* (gene fixed at level $0$); $|P|$ is its size. An edge of $G$ **contradicts** $P$ if it leads to a state in which an activated gene is at $0$ or a repressed gene is at $1$. Given a set of initial states $A$ and a set of states $B \supseteq A$, the network under $P$ has **phenotype $B$** with respect to $A$ if every trajectory from every (perturbed) initial state stays in $B$; it **avoids** a prohibited phenotype $B$ if no such trajectory enters $B$.

**Proposition.** Let $A_P$ be $A$ with activated genes set to $1$ and repressed genes set to $0$, and let $G_P$ be $G$ with all edges contradicting $P$ removed. Then $P$ enforces phenotype $B$ if and only if no state of $V \setminus B$ is reachable from $A_P$ in $G_P$, and $P$ avoids the prohibited phenotype $B$ if and only if no state of $B$ is reachable from $A_P$ in $G_P$. Testing all perturbations of size $i = 0,1,\dots,k$ in increasing order with one breadth-first search each (from a super-source joined to $A_P$ to a super-sink joined from the target states) finds a minimum-size perturbation, or certifies that none of size $\leq k$ exists, in time

$$O\bigl(2^k n^k (|V| + |E|)\bigr),$$

polynomial in the size of the state graph for fixed $k$. Because $|V| = 2^n$, the state graph itself is the bottleneck; encoding each gene by a pair of complementary places in a Petri net and exploring reachable markings with a McMillan unfolding (with perturbations imposed by marking the fixed places and deleting contradicting transitions) answers the same reachability questions on a branching process that is often far smaller than $G$.

## Expansion

Clamping genes only removes transitions that would move a clamped gene off its fixed value, so the dynamics under $P$ is the subgraph $G_P$ started from $A_P$; self-loops are irrelevant. The phenotype condition is a pure reachability property, decided by one breadth-first search in $O(|V| + |E|)$. There are $\sum_{i \leq k}\binom{n}{i}2^i = O(2^k n^k)$ candidate perturbations, and scanning them by increasing size returns a minimum one first (or all minimum ones if the scan finishes the level). In the Petri-net encoding, each regulation function becomes transitions that consume and reproduce tokens on the active place of each regulator it reads and move the token of its target between the target's active and inactive places, so each gene's place pair is invariant and markings correspond to global states. On a probabilistic glioma network model this search singled out one size-one perturbation with the strongest effect on the phenotype.

## Sources

- G. Karlebach, R. Shamir, "Minimally perturbing a gene regulatory network to avoid a disease phenotype: the glioma network as a test case", *BMC Systems Biology* 4 (2010) 15. Methods: the asynchronous GRN model and state graph (Figure 1), perturbations and the minimal-perturbation algorithm with its running time, and the Petri net encoding and unfolding (Figures 2–3); Results: glioma test case. <https://doi.org/10.1186/1752-0509-4-15>. PMCID: PMC2851584.
