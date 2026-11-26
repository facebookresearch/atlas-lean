# Hyperoctahedral group as the symmetry group of Boolean network ensembles

**Setting.** A synchronous Boolean network (BN) on $N$ nodes updates node $i$ by a Boolean function $f_i$ of an ordered list of $K_i$ input nodes. Encoding each state $x\in\{0,1\}^N$ as a basis vector $|x\rangle$ of $\mathbb{R}^{2^N}$, the dynamics is the $2^N\times 2^N$ transition matrix $T=\sum_x |f(x)\rangle\langle x|$, the adjacency matrix of the state-space network (SSN). It factors as $T=MS$, where the *structure matrix* $S=\sum_x|\hat x\rangle\langle x|$ maps a state to the concatenated input vector $\hat x\in\{0,1\}^L$, $L=\sum_i K_i$, and the *logic matrix* $M=\bigotimes_i M_i$ with $M_i=\sum_{\hat x_i}|f_i(\hat x_i)\rangle\langle\hat x_i|$.

A state permutation $G$ acts by $T\mapsto GTG^{-1}$; this always yields an isomorphic SSN (same attractors, periods and basin sizes). $G$ is *admissible* for a BN if $GTG^{-1}=M'S'$ for a structure $S'$ that is a relabeled copy of $S$ (same wiring up to node relabeling and input ordering). For a structure $S$, let $\mathcal{A}(S)$ be the set of state permutations that send every BN with structure $S$ to a BN on one common relabeled copy $S'$.

**Generators.** A *node-flip* $F_b$, $b\in\{0,1\}^N$, maps $|x\rangle\mapsto|x\oplus b\rangle$; a *node-label permutation* $P_\pi$, $\pi\in\mathbb{S}_N$, permutes coordinates. They generate the hyperoctahedral group
$$G_{F,P}=\mathcal{B}_N=(\mathbb{Z}_2)^N\rtimes\mathbb{S}_N,\qquad |G_{F,P}|=2^N N!,$$
the symmetry group of the $N$-cube of states.

**Theorem.**
1. (Admissibility, Theorem 2.) For every structure $S$ and logic matrix $M$, and every $G=F_bP_\pi\in G_{F,P}$, one has $GTG^{-1}=M'S'$ with $S'=P_{\hat\pi}SP_\pi^{-1}$ the relabeled structure and $M'=\bigotimes_i M_i'$, $M_i'=F_{b_i}M_{\pi^{-1}(i)}F_{\hat b_i'}$, where $\hat b_i'$ is the input flip vector of node $i$ in $S'$. Hence $G_{F,P}\subseteq\mathcal{A}(S)$ for all $S$.
2. (Completeness, Theorem 3.) For the directed ring ($N$ nodes, node $i$ reads only node $i-1$ cyclically), $\mathcal{A}(S)=G_{F,P}$. Consequently
$$\bigcap_{S}\mathcal{A}(S)=G_{F,P},$$
the intersection over all structures on $N$ nodes: the state permutations admissible for every BN are exactly compositions of node-flips and node-label permutations.

More generally $\mathcal{A}(S)=G_{F,P}$ whenever no two nodes read the same set of nodes and all nodes read the same number $K$ of distinct nodes, so $G_{F,P}$ is the complete symmetry group of every random-topology ensemble with fixed in-degree $K<N$. It fails for the structure in which every node reads every node including itself, where every state permutation is admissible.

## Expansion

Admissibility of node-flips rests on $F_{\hat b}S=SF_b$ (Proposition 1): flipping a node flips the corresponding entries of every input vector, so the flip can be pushed through $S$ and absorbed into the local logic matrices, which remain valid Boolean functions. Permutations relabel nodes and their input lists. For the converse on the ring, a BN in which $n$ nodes have non-constant functions identifies states in parallel $(N-n)$-dimensional sub-cubes that partition the state cube. Taking $n=N-1$ (one constant node, all others copying their input) the preimage classes are exactly the edges of the cube in one coordinate direction. An admissible $G$ must map these classes for some ring BN to the classes of another ring BN, so it maps edges of the cube to edges, and the edge-preserving permutations of the cube's vertex set form $\mathcal{B}_N$.

Input-label permutations of a node change $S$ and $M$ but not $T$; they are a gauge freedom of the factorization $T=MS$. Combined with the node-flips acting on one node's inputs and output, they generate on each Boolean function of $K$ distinct non-self inputs the Zyklenzeiger group $\mathcal{Z}_K=\mathcal{B}_K\times\mathbb{Z}_2$, explaining why Boolean-function frequencies in ensembles with $G_{F,P}$-invariant weights are constant on $\mathcal{Z}_K$ orbits (14 orbits for $K=3$).

## Sources

- Yi-Kai Mo, Kevin E. Bassler, "State-space symmetry in Boolean network ensembles", arXiv:2611.19639 (2026), Proposition 1, Theorem 2, Theorem 3 and Section III (Eq. for $G_{F,P}=\mathcal{B}_N$), <https://doi.org/10.48550/arXiv.2611.19639>
