# Single-input structural controllability of networks with nodal time constants

**Model.** A network of $N$ nodes with states $x_1,\dots,x_N$ and $P$ external inputs $u_1,\dots,u_P$ evolves by

$$\dot x_i = -p_i x_i + \sum_{k=1}^{N} a_{ik} x_k(t) + \sum_{j=1}^{P} b_{ij} u_j(t), \qquad i = 1,\dots,N,$$

where $a_{ik}$ are the weights of the (directed) adjacency matrix $A$, possibly including self-links $a_{ii}$, $b_{ij}$ are the entries of the input matrix $B \in \mathbb R^{N\times P}$, and $p_i$ is the pole of the intrinsic linear dynamics of node $i$, with time constant $1/p_i$. Equivalently, node $i$ has transfer function $G_i(s) = 1/(s+p_i)$, and in state-space form

$$\dot{\mathbf x}(t) = \hat A \mathbf x(t) + B\mathbf u(t), \qquad \hat A = A - \operatorname{diag}(p_1,\dots,p_N).$$

**Controllability.** The system is controllable iff the Kalman matrix $[\,B,\ \hat A B,\ \dots,\ \hat A^{N-1}B\,]$ has rank $N$. It is *structurally controllable* if the entries of $\hat A$ and $B$ that are not a priori zero can be chosen so that this rank is $N$; by Lin's structural controllability theorem it is then controllable for all such parameter values outside a set of measure zero. The minimum number of driver inputs $N_D$ is the least $P$ for which some input pattern makes the system structurally controllable (one input may feed several nodes).

**Proposition (one input suffices).** For any directed network with the dynamics above in which every node has nonzero intrinsic dynamics or a self-link, i.e. $p_i \ne 0$ or $a_{ii} \ne 0$ for every $i = 1,\dots,N$, the network is structurally controllable with a single input: $N_D = 1$. The input can be taken to drive every node, $B = (1,\dots,1)^{\mathsf T}$.

**Remark (pure integrators cannot be stable).** If instead $p_i = 0$ for all $i$ and the network has no self-links, then $\operatorname{tr}\hat A = 0$, so the eigenvalues of $\hat A$ sum to zero. Such a network of pure integrators can never be asymptotically stable: it is either purely oscillatory or has an eigenvalue with positive real part.

## Expansion

Because generic controllability only needs one witness parameter set, choose $B = (1,\dots,1)^{\mathsf T}$, zero out every off-diagonal edge, and give the (nonzero) diagonal entries of $\hat A$ pairwise distinct values $\lambda_1,\dots,\lambda_N$. The Kalman matrix is then the Vandermonde matrix $[\lambda_i^{k}]_{i, k}$ with $0\le k\le N-1$, which is nonsingular for distinct $\lambda_i$. Lin's theorem lifts this single controllable instance to structural controllability, hence $N_D = 1$.

In graph language, the diagonal terms act as self-loops, and the set of all self-loops is a maximum matching that leaves no node unmatched, so the maximum-matching count of driver nodes also gives one. The large driver-node fractions reported for sparse, heterogeneous real networks arise only if some nodes (in those datasets, all of them) are modeled as pure integrators ($p_i = 0$) without self-links. Degradation of mRNA and protein, birth and death schedules in food webs, and leak currents in neurons all give finite time constants, so the generic assumption is $p_i \neq 0$.

Since controllability is generic, the practically relevant questions are quantitative: whether the system is *almost* uncontrollable (small controllability Gramian eigenvalues, requiring very large inputs), almost unobservable, or has near pole-zero cancellations, which force small stability margins in any output-feedback design.

## Sources

- N. J. Cowan, E. J. Chastain, D. A. Vilhena, J. S. Freudenberg, C. T. Bergstrom, "Nodal dynamics, not degree distributions, determine the structural controllability of complex networks", PLoS ONE 7(6) (2012) e38398, Equations (1)-(4), Proposition 1 and the trace argument following it, <https://doi.org/10.1371/journal.pone.0038398>, PMCID PMC3382243.
