# Degree of monotonicity of a signed network via sign consistency

**Graph of a dynamical system.** For $\dot x = f(x)$ on $\mathbb{R}^n$ where each $\partial f_j/\partial x_i$ has a constant sign, form the signed digraph $G = (V,E,w)$ with $V = \{x_1,\dots,x_n\}$ and, for $i\ne j$, an edge $x_i\to x_j$ of sign $+1$ (resp. $-1$) when $\partial f_j/\partial x_i\ge0$ (resp. $\le 0$) everywhere and is nonzero somewhere. Diagonal terms $\partial f_i/\partial x_i$ give no edge (with $i=j$ allowed, every degradation term would be a negative self-loop, a closed chain of parity $-1$, and $\dot x=-x$, which is monotone, would fail the criterion below); the source's testosterone remark shows that this convention is meant, since it calls the model monotone once the term involving $x_3$ is removed from the first equation, although the degradation terms $-b_ix_i$ remain.

**Monotonicity criterion.** The system is monotone with respect to some orthant order if and only if every closed undirected chain of $G$ (a cycle traversed ignoring edge directions) has parity $+1$. Hence a monotone system has no negative feedback loop and no incoherent feed-forward loop, although these two conditions together are not sufficient. For example, the testosterone model $\dot x_1 = A/(K+x_3) - b_1x_1$, $\dot x_2 = c_1x_1 - b_2x_2$, $\dot x_3 = c_2x_2 - b_3x_3$ contains a negative loop and is not monotone for any orthant order.

**Sign consistency and the degree of monotonicity.** The sign consistency problem asks for a vertex labeling $L:V\to\{-1,1\}$ maximizing the number of consistent edges $F = \{(u,v)\in E: w(u,v) = L(u)L(v)\}$. For $E\ne\emptyset$ and $F$ optimal, the degree of monotonicity is

$$
\mathsf{M} = \frac{|F|}{|E|}\in(0,1],
$$

with $\mathsf{M} = 1$ exactly for orthant-monotone sign structures (for $E=\emptyset$ the ratio is $0/0$ and $\mathsf{M}$ is undefined). This corrects Section 5 of the source, which prints that the normalization "ensures that $0<\mathsf{M}<1$": the value $\mathsf{M}=1$ is attained by every network whose closed undirected chains all have parity $+1$.

## Proof sketch

A vertex labeling $L$ corresponds to the orthant order $\preceq_s$ with $s = L$; an edge is consistent when it respects that order. If all undirected cycles have parity $+1$, a labeling with all edges consistent exists (propagate signs along a spanning forest), which is the classical Kamke-type condition for monotone systems; otherwise $1-\mathsf{M}$ is the minimum fraction of edges whose removal makes the system monotone. Maximizing $|F|$ is a MAX-CUT-type problem; the source computes a labeling by a Goemans–Williamson-style semidefinite-programming relaxation. Empirically, across signaling networks, $\mathsf{M}$ is strongly negatively correlated with the topological redundancy $\mathcal{R}_{\mathrm{new}}$: more redundant networks are less monotone.

## Related topics

- [Topological redundancy of a signed network via binary transitive reduction](topological-redundancy-via-binary-transitive-reduction.md)

## Sources

- Réka Albert, Bhaskar DasGupta, Rashmi Hegde, Gowri Sangeetha Sivanathan, Anthony Gitter, Gamze Gürsoy, Pradyut Paul and Eduardo Sontag, "Computationally efficient measure of topological redundancy of biological and social networks", *Physical Review E* 84 (2011), 036117, <https://doi.org/10.1103/physreve.84.036117>. Preprint version: arXiv:1108.6113 (2011), Section 5 (orthant-monotonicity lemma quoted from DasGupta, Enciso, Sontag and Zhang 2007, the sign consistency problem and the measure of monotonicity) and Section 7 (correlation between redundancy and monotonicity), <https://doi.org/10.48550/arXiv.1108.6113>.
