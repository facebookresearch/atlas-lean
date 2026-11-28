# Solving semirandom planted CSPs at the refutation threshold

For every constant arity $k$, a polynomial-time algorithm finds an assignment satisfying a $1-\epsilon$ fraction of the constraints of a semirandom planted $k$-CSP once it has about $n^{k/2}\log^3 n/\epsilon^9$ constraints: the search problem is solvable at the same threshold as refutation, with worst-case scopes and an arbitrary planted assignment.

Let $P:\{\pm1\}^k\to\{0,1\}$ be a predicate. A CSP instance $\Psi$ with predicate $P$ has constraints $P(\ell(\vec{C})_1x_{\vec{C}_1},\dots,\ell(\vec{C})_kx_{\vec{C}_k})=1$ for $\vec{C}$ in a multiset $\vec{\mathcal{H}}\subseteq[n]^k$ of scopes, with literal negations $\ell(\vec{C})\in\{\pm1\}^k$; $\mathrm{val}_\Psi(x)$ is the fraction of constraints satisfied by $x\in\{\pm1\}^n$. A distribution $Q$ on $\{\pm1\}^k$ is a **planting distribution for $P$** if $\Pr_{y\sim Q}[P(y)=1]=1$. A **semirandom planted instance** is drawn from $\Psi(\vec{\mathcal{H}},x^*,Q)$, where the scopes $\vec{\mathcal{H}}$ and the planted assignment $x^*\in\{\pm1\}^n$ are arbitrary and, independently for each $\vec{C}\in\vec{\mathcal{H}}$, the literal negations are drawn with

$$
\Pr[\ell(\vec{C})=\ell]=Q(\ell\odot x^*_{\vec{C}})\qquad(\ell\in\{\pm1\}^k),
$$

where $\odot$ is the entrywise product. Then $x^*$ satisfies $\Psi$ with probability $1$.

**Theorem.** Let $k\in\mathbb{N}$ be constant. There is a polynomial-time algorithm that takes as input a $k$-CSP $\Psi$ and outputs an assignment $x$ with the following guarantee. If $\Psi$ is a semirandom planted $k$-CSP drawn from $\Psi(\vec{\mathcal{H}},x^*,Q)$ with

$$
m\ge c^k\,n^{k/2}\cdot\frac{\log^3 n}{\epsilon^9}
$$

constraints, where $c$ is a universal constant, then with probability $1-1/\mathrm{poly}(n)$ over $\Psi$ the output satisfies $\mathrm{val}_\Psi(x)\ge1-\epsilon$. In particular, with $\epsilon=1/\mathrm{polylog}(n)$ and $m\ge\tilde{O}(n^{k/2})$, the output satisfies a $1-o(1)$ fraction of the constraints with high probability.

The proof goes through **noisy planted $k$-XOR** for $k\ge 2$ (footnote 10 of the source notes that Theorem 3 applies for $|S|\ge 2$, while $k=1$ is handled separately by Lemma C.1 with $m\ge O(n\log n/\epsilon)$): for a $k$-uniform hypergraph $\mathcal{H}\subseteq\binom{[n]}{k}$ ($k\ge 2$), $x^*\in\{\pm1\}^n$ and $\eta\in[0,1/2)$, the instance $\psi\sim\psi(\mathcal{H},x^*,\eta)$ contains, for each $C\in\mathcal{H}$, the constraint $\prod_{i\in C}x_i=\prod_{i\in C}x^*_i$ with probability $1-\eta$ and $\prod_{i\in C}x_i=-\prod_{i\in C}x^*_i$ otherwise (a corrupted constraint; $\mathrm{Err}_\psi$ is the set of corrupted constraints). Let $k\ge 2$, $\epsilon\in(0,1)$ and

$$
m\ge c\,n^{k/2}\cdot\frac{k^4\log^3 n}{\epsilon^5(1-2\eta)^4}
$$

for a universal constant $c$. There is a polynomial-time algorithm that, on a $k$-XOR instance $\psi$ with constraint hypergraph $\mathcal{H}$, outputs disjoint sets $\mathrm{Alg}_1(\mathcal{H}),\mathrm{Alg}_2(\psi)\subseteq\mathcal{H}$ such that (1) for every instance with $m$ constraints, $|\mathrm{Alg}_1(\mathcal{H})|\le\epsilon m$ and $\mathrm{Alg}_1(\mathcal{H})$ depends only on $\mathcal{H}$, and (2) for every $x^*$ and every $k$-uniform $\mathcal{H}$ with at least $m$ hyperedges, with probability at least $1-1/\mathrm{poly}(n)$ over $\psi\sim\psi(\mathcal{H},x^*,\eta)$, $\mathrm{Alg}_2(\psi)=\mathrm{Err}_\psi\cap(\mathcal{H}\setminus\mathrm{Alg}_1(\mathcal{H}))$.

## Expansion

Exact recovery of $x^*$ is impossible in this model (variables that occur in no scope are undetermined), and satisfying all constraints would also solve instances with $O(n)$ constraints hidden among the others, so a $1-o(1)$ fraction is qualitatively optimal. Refutation does not transfer directly to search here: already for semirandom 2-XOR several far-apart assignments can be optimal, which breaks both certificates of near-uniqueness and top-eigenvector recovery.

The algorithm reduces the planted CSP to noisy $k$-XOR instances, one per subset of coordinates, then reduces each $k$-XOR instance to spread bipartite instances via a hypergraph decomposition. Its key step is an efficiently checkable certificate that the planted solution is the unique solution of a semidefinite program: if the Laplacian of an associated graph is relatively spectrally approximated by a correlated random subsample (the uncorrupted constraints), the SDP solution is unique and equals the planted one. Matrix Chernoff bounds establish this relative approximation when the constraint graph is a weak spectral expander and the number of constraints exceeds about $n^{k/2}$; expander decomposition splits an arbitrary hypergraph into such pieces plus an $\epsilon$ fraction of discarded constraints, and on the remaining constraints the corrupted ones are identified exactly, so the cleaned subinstance is satisfiable and solvable by Gaussian elimination; a consistent patching scheme combines the solutions across pieces. This is the search counterpart of [strong refutation of semirandom CSPs](semirandom-csp-strong-refutation.md), and the algorithm also nearly inverts Goldreich's local pseudorandom generators with $\tilde{\Omega}(n^{k/2})$ stretch on any hypergraph.

## Depends on

- [Semirandom and smoothed CSP instances and strong refutation](semirandom-and-smoothed-csps.md)

## Proof depends on

None.

## Sources

- Venkatesan Guruswami, Jun-Ting Hsieh, Pravesh K. Kothari, Peter Manohar, "Efficient Algorithms for Semirandom Planted CSPs at the Refutation Threshold", *FOCS 2023*, 2023, arXiv:2309.16897v1, https://arxiv.org/abs/2309.16897 (Definitions 1.1, 1.2 and 1.3; Theorem 2, the formal version of Theorem 1; Theorem 3; Lemma 2.4 and Lemma 5.2 for the proof outline).
