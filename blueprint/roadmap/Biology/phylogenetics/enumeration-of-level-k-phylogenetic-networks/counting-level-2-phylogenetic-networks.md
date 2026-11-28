# Counting level-2 phylogenetic networks

Use the definitions of binary rooted and unrooted phylogenetic networks from [counting level-1 phylogenetic networks](counting-level-1-phylogenetic-networks.md): no redundant *nontrivial* bridgeless components, the one-vertex rooted network on a single leaf, and connected unrooted networks on at least two leaves. A rooted network has **level 2** if every bridgeless component contains at most two reticulations; an unrooted network has level 2 if a tree is obtained by deleting at most two edges from each bridgeless component and suppressing degree-2 vertices. Each nontrivial bridgeless component of a rooted level-2 network contracts to one of the finitely many level-1 or level-2 **generators** (directed multigraphs obtained by deleting the outgoing cut arcs and contracting in-degree-1 out-degree-1 vertices).

**Theorem (unrooted level-2).** For $n \ge 1$ let $u_n$ be the number of unrooted level-2 networks with $n + 1$ labelled leaves and $U(z) = \sum_{n \ge 1} u_n z^n/n!$. Then

$$U = z\,\varphi(U), \qquad \varphi(u) = \frac{1}{1 - \dfrac{3u^5 - 16u^4 + 32u^3 - 30u^2 + 12u}{4(1-u)^4}},$$

hence $u_n = (n-1)!\,[u^{n-1}]\,\varphi(u)^n$. The sequence $(u_n)_{n \ge 1}$ begins $1, 6, 135, 5052, 264270$, and

$$u_n \sim c_1\, c_2^{\,n}\, n^{n-1}, \qquad c_1 \approx 0.07695,\ c_2 \approx 5.4925,$$

where $\tau \approx 0.12117$ is the root of $\varphi(\tau) = \tau\varphi'(\tau)$ in the disk of convergence of $\varphi$ and the singularity of $U$ is $\rho = \tau/\varphi(\tau) \approx 0.06698$.

**Theorem (rooted level-2).** For $n \ge 1$ let $\ell_n$ be the number of rooted level-2 networks with $n$ labelled leaves ($\ell_1 = 1$ counts the one-vertex network) and $L(z) = \sum_{n \ge 1} \ell_n z^n/n!$. Then

$$L = z\,\varphi_2(L), \qquad \varphi_2(u) = \frac{1}{1 - \dfrac{36u - 102u^2 + 159u^3 - 148u^4 + 81u^5 - 24u^6 + 3u^7}{4(1-u)^6}},$$

hence $\ell_n = (n-1)!\,[u^{n-1}]\,\varphi_2(u)^n$. The sequence $(\ell_n)_{n \ge 1}$ begins $1, 18, 1143, 120078, 17643570, 3332111850$, and

$$\ell_n \sim c_1\, c_2^{\,n}\, n^{n-1}, \qquad c_1 \approx 0.02931,\ c_2 \approx 15.433,$$

where $\tau \approx 0.04447$ is the root of $\varphi_2(\tau) = \tau\varphi_2'(\tau)$ in the disk of convergence of $\varphi_2$ and the singularity of $L$ is $\rho = \tau/\varphi_2(\tau) \approx 0.02384$.

In both cases, for a network drawn uniformly at random from the networks of fixed size $n$ (rooted level-2 networks with $n$ labelled leaves, or unrooted ones with $n + 1$), the number of nontrivial bridgeless components and the number of edges inside them are asymptotically normal, with mean and variance linear in $n$ up to $O(1)$.

## Depends on

- [Counting level-1 phylogenetic networks](counting-level-1-phylogenetic-networks.md)

## Proof depends on

- [Lagrange–Bürmann formula from the fixed-point equation alone](../../../RingTheory/formal-power-series/lagrange-inversion-theorem/fps-lagrange-burmann-coeff.md)

## Expansion

The decomposition is the level-1 one with each cycle replaced by a generator: a bridgeless component is a generator whose sides (arcs, and for some generators a choice among parallel arcs) carry possibly empty sequences of hanging subnetworks, each contributing a factor $1/(1-L)$, and the outgoing reticulation arcs carry nonempty subnetworks. Collecting the four level-2 generators together with the level-1 cycle and the tree vertex gives the equation $L = z\varphi_2(L)$; the Lagrange–Bürmann formula with $g = X$ yields the exact counts and the singular inversion theorem yields the $c_1 c_2^n n^{n-1}$ asymptotics with $c_2 = 1/(e\rho)$. The unrooted equation is derived the same way after rooting at a distinguished leaf.

## Sources

- M. Bouvel, P. Gambette and M. Mansouri, "Counting phylogenetic networks of level 1 and 2", Journal of Mathematical Biology (2020), Sections 2.3, 6 and 7 (Theorem 6.1, Propositions 6.2, 6.3, Theorem 7.1, Propositions 7.2, 7.3, Table 2), <https://doi.org/10.1007/s00285-020-01543-5>.
