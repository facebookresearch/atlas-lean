# Uniform stationary law and tree balance process of the evolving Moran genealogy

**Setting.** A neutral Moran population of fixed size $n \ge 2$ evolves in discrete steps: choose $k, l \in \{1,\dots,n\}$ uniformly and independently; if $k \ne l$, individual $l$ dies and individual $k$ duplicates. The genealogy of the current population, with branch lengths discarded and the $n-1$ internal nodes labelled $1,\dots,n-1$ in the order of the splits they represent, is an ordered binary **increasing tree**; let $\mathcal{T}_n$ be the set of such trees, $|\mathcal{T}_n| = (n-1)!$. One Moran step maps $T_i$ to $T_{i+1} = \Phi_{k,l}(T_i)$: delete leaf $l$ with its pendant branch and attachment node, relabel the later nodes down by one, and split leaf $k$ into a cherry labelled $n-1$. The Markov chain $(T_i)$ is the **evolving Moran genealogy (EMG)**.

**Theorem.**

*(1)* (Sample-subtree invariance.) If $T$ is a Yule tree of size $n$ and $S$ is a uniform $k$-subset of its leaves, the induced subtree $T_S$ is uniform on $\mathcal{T}_k$: $\Pr(T_S = \tilde T) = 1/(k-1)!$. Successive random grafting of leaves generates the same uniform law on $\mathcal{T}_n$.

*(2)* (Stationarity.) The EMG is an irreducible aperiodic chain on $\mathcal{T}_n$ whose stationary law is uniform, $P^\ast(T) = 1/(n-1)!$; the process run backward in time is again a Markov chain, with transition probabilities obtained by reversing the arrows: $\Pr_{\mathrm{EMG}}(T_{j+1} = T' \mid T_j = T) = \Pr_R(\tilde T_{i+1} = T \mid \tilde T_i = T')$.

*(3)* (Tree balance process.) Let $L_i = |T_i^l|$ be the number of leaves in the left subtree of the root. For $2 \le L_i \le n-2$,

$$\Pr(L_{i+1} = L_i \pm 1 \mid L_i) = \frac{L_i(n - L_i)}{n^2}, \qquad \Pr(L_{i+1} = L_i \mid L_i) = \frac{L_i^2 + (n - L_i)^2}{n^2},$$

while from $L_i = 1$ the chain moves to $2$ with probability $1/n$, stays with probability $((n-1)^2 + 2)/n^2$, and jumps to each other value with probability $1/n^2$ (symmetrically at $n-1$).

*(4)* (MRCA jumps.) The times at which the most recent common ancestor of the population changes form a geometric jump process with per-step intensity $2/n^2$; between the birth of an individual whose descendants eventually fix and that fixation, the expected number of MRCA jumps is $2 - 2/n$.

## Depends on

- [Neutral Moran genealogy as a relabeled Cannings model](../../../population-genetics/moran-model/moran-model-genealogy-per-step-c-2-n-2-and-time.md)
- [Random joining](../random-joining.md)

## Expansion

At every step the current genealogy can be read as the outcome of a Yule process, because the last split always involves a uniformly chosen lineage and deletions of uniform leaves preserve uniformity (part 1); uniformity of $P^\ast$ then follows, and with a uniform stationary law the time reversal simply transposes the transition matrix. Away from the boundary, $L_i$ changes only if the killed and duplicated individuals lie on opposite sides of the root, giving the symmetric birth-death probabilities above. When one side of the root holds a single leaf, its death removes the root and the new root split is the old left or right child, which explains the long jumps of probability $1/n^2$; such root replacements are exactly the MRCA jumps, which occur when the lone lineage on one side of the root dies, and $L_i \in \{1, n-1\}$ is visited at a rate that makes the jump intensity $2/n^2$. The tree balance process is closely related to Aldous's $\Omega_1$ balance statistic followed through time.

## Sources

- Johannes Wirtz and Thomas Wiehe, *The evolving Moran genealogy*, Theor. Popul. Biol. 130 (2019), 94–105. <https://doi.org/10.1016/j.tpb.2019.07.005> Definitions 2–7, Lemmas 1–5, Corollaries 1–2 and Proposition 1. Locators use the numbering of the preprint arXiv:1808.10809.
