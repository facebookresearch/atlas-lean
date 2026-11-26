# Burnside count of Boolean network symmetry orbits

**Setting.** Fix a structure $S$ of a synchronous Boolean network on $N$ nodes with in-degrees $K_i$ and automorphism group $\mathrm{Aut}(S)$ (node-label permutations mapping $S$ onto itself, possibly reordering input links). Let $\mathcal{M}$ be the set of logic matrices on $S$, so $|\mathcal{M}|=\prod_i 2^{2^{K_i}}$, and let the expanded ensemble $\mathcal{E}$ consist of all pairs $(M,S')$ with $S'$ a relabeled copy of $S$, so $|\mathcal{E}|=\frac{N!}{|\mathrm{Aut}(S)|}|\mathcal{M}|$. The hyperoctahedral group $G_{F,P}=(\mathbb{Z}_2)^N\rtimes\mathbb{S}_N$ of node-flips and node-label permutations acts on $\mathcal{E}$; members of one orbit have isomorphic state-space networks.

**Statement.** The number of orbits is

$$|\mathcal{E}/G_{F,P}|=\frac{1}{2^N|\mathrm{Aut}(S)|}\sum_{\pi\in\mathrm{Aut}(S)}\ \sum_{b\in\{0,1\}^N}\big|\mathcal{M}^{F_bP_\pi}\big|,$$

where $\mathcal{M}^{g}$ is the set of logic matrices fixed by $g$. For $g=F_bP_\pi$, $g$ moves each input state of node $j$ to an input state of node $\pi(j)$, complementing the output if $\pi(j)$ is flipped; the input states of all nodes thus fall into $C(g)$ cycles. Call a cycle odd if the output is complemented an odd number of times around it. Then

$$\big|\mathcal{M}^{g}\big|=\begin{cases}2^{C(g)} & \text{if every cycle is even},\\ 0 & \text{otherwise}.\end{cases}$$

**Example.** For the directed ring with $N=3$ ($K_i=1$, $|\mathcal{M}|=64$, $|\mathrm{Aut}(S)|=3$, $|\mathcal{E}|=128$) the count gives $5$ orbits: $n=0,1,2$ non-constant functions, and $n=3$ with an even or odd number of negations, of sizes $16,48,48,8,8$. These five classes have pairwise non-isomorphic state-space networks.

## Depends on

- [Hyperoctahedral group as the symmetry group of Boolean network ensembles](hyperoctahedral-group-as-the-symmetry-group-of-boolean-network-ensembles.md)

## Expansion

Burnside's lemma gives $|X/G|=|G|^{-1}\sum_g|X^g|$. An element $F_bP_\pi$ can fix a representation only if $\pi$ maps the copy $S'$ to itself, and all $N!/|\mathrm{Aut}(S)|$ copies contribute equally, which reduces the sum to $\pi\in\mathrm{Aut}(S)$ on $S$ itself. A fixed logic matrix must take, at each input state, the output it takes at the preceding input state of the cycle (complemented across a flip), so one free bit per cycle remains, unless going once around the cycle forces a bit to equal its own complement. In spin language each cycle is a closed loop of ferromagnetic and antiferromagnetic bonds, and an odd cycle is frustrated. For the fully connected structure without self-inputs the orbits reproduce Glass's classical counts (4 for $N=2$, 112 of the 4096 networks for $N=3$).

## Sources

- Yi-Kai Mo, Kevin E. Bassler, "State-space symmetry in Boolean network ensembles", arXiv:2611.19639 (2026), Appendix C (orbit count reduced to $\mathrm{Aut}(S)$, counting by cycles of input states, and the $N=3$ directed ring example), <https://doi.org/10.48550/arXiv.2611.19639>
