# Node-safe walks for metagenomic reconstructions

Let $G$ be a strongly connected directed graph. A **node-covering metagenomic reconstruction** of $G$ is a collection $\mathcal R$ of circular walks in $G$ such that every node lies on some walk in $\mathcal R$. A walk $w$ is **node-safe** if for every such $\mathcal R$ some $C \in \mathcal R$ contains $w$ as a subwalk. A walk $w = (v_0, e_0, v_1, \dots, v_t, e_t, v_{t+1})$ is a **node-omnitig** if (i) for all $1 \le i \le j \le t$ there is no proper $v_j$–$v_i$ path whose first edge differs from $e_j$ and whose last edge differs from $e_{i-1}$, and (ii) for every $0 \le j \le t$ the edge $e_j$ is the only $v_j$–$v_{j+1}$ path. A node $x$ is a **certificate** of $w$ if $w$ is a subwalk of every cycle through $x$.

**Theorem.** A walk $w$ in a strongly connected graph $G$ is node-safe if and only if $w$ is a node-omnitig and $w$ has at least one certificate (Obscura Acosta, Mäkinen and Tomescu 2018, Theorem 2). For a proper node-omnitig, $\operatorname{Cert}(w) = \bigcap_{i=0}^{t+1} \operatorname{Cert}(v_i)$ (Lemma 6), and all node-safe walks can be reported in $O(m^2 + n^3)$ time for $n$ nodes and $m$ edges (Theorem 12).

The certificate condition is what distinguishes the metagenomic setting from the single-genome one: for a strongly connected graph other than a single cycle, the walks contained in every node-covering circular walk are exactly the node-omnitigs (Theorem 1, due to Tomescu and Medvedev), but a collection of circular walks can avoid an omnitig by covering its region with short cycles that bypass it.

## Depends on

- [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md)

## Expansion

($\Rightarrow$) If (i) fails, any circular walk using $w$ can be rerouted along the forbidden $v_j$–$v_i$ path so that $w$ no longer appears; if (ii) fails, the alternative $v_j$–$v_{j+1}$ path gives the same rerouting. If $w$ has no certificate, take for every node a cycle through it that avoids $w$; this collection is a reconstruction in which $w$ never appears. ($\Leftarrow$) Any reconstruction must cover a certificate $x$ with some circular walk $C$. If $C$ is a cycle, it contains $w$ by definition of certificate. Otherwise let $G[C]$ be the subgraph formed by the edges of $C$, which is strongly connected and covered by $C$. The shortest proper circular sub-walk of $C$ through $x$ is a cycle through $x$, so it contains $w$ and $w$ is a walk in $G[C]$; both omnitig conditions survive deleting edges, so $w$ is a node-omnitig of $G[C]$, and Theorem 1 applied to $G[C]$ (or, if $G[C]$ is a single cycle, the fact that $C$ then winds around that cycle, which contains $w$) shows that $w$ is a subwalk of $C$. The algorithm builds one node-covering circular walk $C$ of length at most $n^2$, then extends safe windows $C(i,k)$ incrementally, testing the omnitig and certificate conditions.

## Sources

- N. Obscura Acosta, V. Mäkinen and A. I. Tomescu, *A safe and complete algorithm for metagenomic assembly*, Algorithms for Molecular Biology 13 (2018), 3, Definitions 1–3 and 5, Theorems 1 and 2, Lemma 6 and Theorem 12. <https://doi.org/10.1186/s13015-018-0122-7> (PMCID: PMC5802251)
