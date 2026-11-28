# NNI diameter bounds for tiers of phylogenetic networks

**Setting.** A (unrooted binary phylogenetic) *network* on a finite set $X$ with $|X| = \ell \ge 3$ is a connected graph in which every vertex has degree 1 or 3 and whose leaves are labeled bijectively by $X$. Its reticulation number is $r(N) = |E(N)| - |V(N)| + 1$. Tier $i$, written $N_i(X)$, consists of the networks with $n = 2(\ell + i - 1)$ vertices; a network lies in $N_i(X)$ if and only if $r(N) = i$, and then $|E(N)| = 2\ell - 3 + 3i$ (tier 0 is the set of binary trees). An *NNI* operation on a path $v_1v_2v_3v_4$ through degree-3 vertices $v_2, v_3$ replaces it by $v_1v_3v_2v_4$, and stays within a tier; a *triangle* operation moves between tiers $i$ and $i+1$. NNI and triangle operations connect all networks on $X$, so they define a metric $d$ on $N(X) = \bigcup_i N_i(X)$, and NNI alone connects each tier. Let $\Delta_i$ be the NNI diameter of $N_i(X)$.

**Theorem.** Let $i \ge 1$.
1. (Size) $|N_i(X)| \ge (\ell + i - 3)!/(i-1)!$, and $|N_1(X)| \ge (\ell-2)!\,2^{\ell-3}$.
2. (Neighborhood growth) From any network in $N_i(X)$, at most $6^{\,2(\ell+i-1) + 10m} = 6^{\,n + 10m}$ networks of the tier are reachable in $m$ or fewer NNI operations.
3. (Lower bound) $\Delta_i$ is bounded below by a term of order $n\log n$; explicitly, combining parts 1 and 2 gives $6^{\,n + 10\Delta_i} \ge (n/2 - 2)!/(i-1)!$, and Stirling's formula turns this into an $n\log_6 n$ bound.
4. (Upper bound) $\Delta_i \le 3n + \binom{n/2 + i - 1}{2} - 2$.
5. (Across tiers) If $N \in N_i(X)$ and $N' \in N_j(X)$ with $0 \le i \le j$, then $d(N, N') \le 6\ell + 7j - i - 8 + \binom{\ell + 2j - 2}{2}$.

## Expansion

The size bound counts *echidna graphs*: a cycle carrying the $\ell$ leaves and $i - 1$ chords, distinct chord sequences giving non-isomorphic networks. The neighborhood bound uses a graph-grammar encoding of NNI sequences (Sleator, Tarjan and Thurston), as in the tree case. Since all of $N_i(X)$ is reachable within $\Delta_i$ steps, $6^{n + 10\Delta_i} \ge |N_i(X)|$. For the upper bound, any tier-$i$ network becomes simple (no non-trivial cut-edges; there are at most $\ell + i - 3$ of them) in at most $\ell + i - 3 = n/2 - 1$ NNI moves and then *pseudo-Hamiltonian* (a cycle through all non-leaf vertices) in at most $n$ more; two pseudo-Hamiltonian networks differ by a permutation of the labeled vertices on a cycle of length $n/2 + i - 1$, sortable by at most $\binom{n/2+i-1}{2}$ adjacent swaps, each an NNI. Across tiers, $j - i$ triangle operations reach tier $j$ first.

## Sources

- A. Francis, K. T. Huber, V. Moulton, T. Wu, "Bounds for phylogenetic network space metrics", Journal of Mathematical Biology (2018), Lemmas 1–6, Propositions 1–3, Theorems 1–3, Corollaries 2–4, <https://doi.org/10.1007/s00285-017-1171-0>, PMCID PMC5829221.
