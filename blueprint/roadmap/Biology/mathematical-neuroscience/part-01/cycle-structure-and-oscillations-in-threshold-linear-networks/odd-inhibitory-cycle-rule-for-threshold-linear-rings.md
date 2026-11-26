# Odd inhibitory cycle rule for threshold-linear rings

**Threshold-linear network.** $\mathrm{TLN}(W,b)$ on nodes $[n]=\{1,\dots,n\}$ evolves by

$$\dot x_i=-x_i+\Big[\sum_{j=1}^nW_{ij}x_j+b_i\Big]_+,\qquad i\in[n],$$

with $[\cdot]_+=\max\{\cdot,0\}$ and constant inputs $b_i$. Each node is excitatory or inhibitory; $\delta_{j,I}=1$ if $j$ is inhibitory and $0$ otherwise, and an edge $i\leftarrow j$ of a directed graph $G$ carries weight $W_{ij}=w_{ij}(-1)^{\delta_{j,I}}$ with $w_{ij}>0$ ($W_{ij}=0$ off $G$).

**Ring setting.** Let $G$ be the directed cycle $1\to2\to\dots\to n\to1$ with $n_I\ge1$ inhibitory and $n_E$ excitatory nodes, $n=n_I+n_E\ge2$ ($\ge3$ if $n_I=1$), and $W_{i,i-1}=w_{i-1}(-1)^{\delta_{i-1,I}}$ with $w_j>0$ (indices mod $n$). Let $a_1<\dots<a_{n_I}$ be the nodes whose predecessor is inhibitory (cyclically, $a_{n_I+1}=a_1$), with inputs $b_{a_k}>0$, and $b_i=0$ for the other nodes. Assume the initial state satisfies $x_j(0)\in[0,\;b_{a_k}\prod_{i=a_k}^{j-1}w_i]$ for $a_k\le j<a_{k+1}$ (empty products equal $1$). Consider

$$\text{(4)}\ \ \prod_{i=a_k}^{a_{k+1}-1}w_i<\frac{b_{a_{k+1}}}{b_{a_k}}\ \ \forall k,\qquad \text{(5)}\ \ \prod_{i=a_k}^{a_{k+1}-1}w_i>\frac{b_{a_{k+1}}}{b_{a_k}}\ \ \forall k,\qquad \text{(6)}\ \ \Big(\prod_{i=1}^nw_i\Big)^{1/n}<\frac1{\cos(\pi/n)},\qquad \text{(7)}\ \ \Big(\prod_{i=1}^nw_i\Big)^{1/n}>\frac1{\cos(\pi/n)}.$$

**Theorem 2.** Trajectories stay in the initial box for all $t\ge0$ (Lemma 1), and:

- if $n_I$ is **even**: under (4) there is a unique globally asymptotically stable fixed point with full support $[n]$; under (5) there are two asymptotically stable fixed points whose supports are strict complementary subsets of $[n]$;
- if $n_I$ is **odd**: under (4) the unique fixed point (full support) is globally asymptotically stable; under (5) and (6) the unique fixed point (full support) is asymptotically stable but not globally; under (5) and (7) the unique fixed point (full support) is unstable.

Hence a bounded ring with an odd number of inhibitory nodes and loop gain satisfying (5) and (7) has no stable fixed point, so its long-term behavior is a limit cycle, quasi-periodic or chaotic. With equal weights $w$ and equal inputs, the thresholds are $w=1$ and, for odd $n_I$, $w=1/\cos(\pi/n)$.

## Expansion

Condition (4) forces the geometric mean of the weights below $1$ and (5) above $1$. For a full-support fixed point all rectifications are inactive, and the Jacobian is $-I+W$ with $W$ a weighted cyclic permutation; its eigenvalues are $-1+\rho\,\omega$ where $\rho=(\prod w_i)^{1/n}$ and $\omega$ ranges over the $n$-th roots of $(-1)^{n_I}$. For even $n_I$ these include $\omega=1$, so the fixed point loses stability through a real eigenvalue at $\rho=1$, which gives bistability between complementary supports (winner-take-all); for odd $n_I$ the roots are $e^{i\pi(2m+1)/n}$, the rightmost having real part $\cos(\pi/n)$, so stability is lost through a complex pair at $\rho=1/\cos(\pi/n)$, the signature of oscillation. Thus an odd number of inhibitory links in the loop (net negative feedback) is necessary, as in Thomas's conjecture, but not sufficient: the loop must also be strong enough. Positive inputs to excitatory nodes can silence the next inhibited node permanently and break the cycle. Applied to basal ganglia circuits, cortex–basal ganglia connectivity contains several odd inhibitory cycles, most passing through the external globus pallidus, consistent with pallidal (rather than subthalamic) inhibition quenching pathological beta oscillations.

## Depends on

- [Acyclic threshold-linear networks have a globally stable fixed point](acyclic-threshold-linear-networks-have-a-globally-stable-fixed-point.md)

## Sources

- Zang J, Liu S, Helson P, Kumar A, "Structural constraints on the emergence of oscillations in multi-population neural networks" (2024), Theorem 2, conditions (3)-(9), Lemma 1, Remarks 1-3 and the basal ganglia application, <https://doi.org/10.7554/elife.88777>, PMCID PMC10937037.
