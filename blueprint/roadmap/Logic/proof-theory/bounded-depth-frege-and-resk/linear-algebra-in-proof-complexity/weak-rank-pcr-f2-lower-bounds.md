# Weak rank lower bounds and generators for PCR over $\mathbb F_2$

For every $m>n$ and $A\in\{0,1\}^{m\times m}$, $\mathrm{PCR}_{\mathbb F_2}$ refutations of the algebraic and of the bamboo-tree encoding of the weak rank principle need size $2^{\Omega(n)}$. For $m>2n$ this makes $(X,Y)\mapsto XY$ a proof complexity generator stretching $2nm$ bits to $m^2$, and iterated versions of both encodings give function generators.

Here the encodings $\mathrm{Rank}^m_n(A)$ and $\mathrm{BTRank}^m_n(A)$ are those of the [weak rank principle](weak-rank-principle.md) over the expressed field $\mathbb F_2$, refuted in [$\mathrm{PCR}_{\mathbb F_2}$](polynomial-calculus-resolution.md), with size the number of monomials; a refutation exists only when the system is unsatisfiable, that is when $A$ is not a product $XY$ over $\mathbb F_2$.

**Theorem (algebraic encoding).** For every $m>n$ and $A\in\mathbb F_2^{m\times m}$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of $\mathrm{Rank}^m_n(A)$ requires size $2^{\Omega(n)}$.

**Theorem (bamboo-tree encoding).** For every $m>n$ and $A\in\mathbb F_2^{m\times m}$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of $\mathrm{BTRank}^m_n(A)$ requires size $2^{\Omega(n)}$.

**Generators.** A *proof complexity generator* is a map $g:\{0,1\}^k\to\{0,1\}^\ell$ with $k<\ell$; it is hard for a proof system when, for every $b\in\{0,1\}^\ell$, the encoding of "$b\notin\mathrm{Range}(g)$" has no short refutation, and it is a *function generator* when its stretch $\ell$ is $2^{k^{\Omega(1)}}$. The rank generator $g(X,Y)=XY$ maps $\mathbb F_2^{2mn}$ to $\mathbb F_2^{m^2}$ and stretches exactly when $m>2n$. For $m>2n$, both theorems therefore say that $g$ is a proof complexity generator for $\mathrm{PCR}_{\mathbb F_2}$, under the algebraic and under the bamboo-tree encoding, stretching $2nm$ bits into $m^2$.

**Iterated encodings.** Copies of the rank system are indexed by strings $\pi$ of length at most $\kappa$ over a finite alphabet $\Sigma$, and every entry of the right-hand side $A^{(\pi)}$ is a Boolean constant or an input variable of a copy indexed by a strictly longer string (so the copies with $|\pi|=\kappa$ have constant right-hand sides).

1. The iterated rank system $\mathrm{IRank}^m_n(\mathbf A,\kappa,\Sigma)$ is the polynomial system $\bigcup_{\pi}\{X^{(\pi)}Y=A^{(\pi)}\}$, with a separate variable matrix $X^{(\pi)}$ for each $\pi$ and one shared $Y$. If $\kappa>0$, $m>n\ge16+192(\kappa+2)$ and $192(\kappa+2)$ divides $n-16$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of it requires size $2^{\Omega(\sqrt{n/\kappa})}$.
2. The iterated bamboo-tree system $\psi_G(\mathbf A,\kappa)$ takes $\Sigma=\{0,1\}$ and an $m\times n$ bipartite graph $G$; each $\pi$ has four bamboo-tree copies of the rank system whose $Y$-entries $y_{k,j}$ exist only for $k$ adjacent to $j$ in $G$, and the parity of their four outputs is set equal to $A^{(\pi)}_{i,j}$ through a balanced tree of extension variables. For $N=8n+8$, $m=16(N+2)$, $\kappa\le n^{\alpha}$ with $\alpha<1$, and $G$ an $(n^{\delta},d)$-lossless expander with left degrees between $50\log n$ and $150\log n$ and $\delta>4\alpha$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of $\psi_{P(H(G))}(\mathbf A,\kappa)$, for the source's graph transformations $P$ and $H$, requires size $2^{\Omega((n^{\delta}/\kappa)^{1/3})}$.

With these iterated encodings both the algebraic and the bamboo-tree rank generators become function generators with stretch $2^{n^{\Omega(1)}}$ that are hard for $\mathrm{PCR}_{\mathbb F_2}$.

## Expansion

The algebraic bound uses random restrictions to reduce size to degree, then a degree lower bound for the restricted rank system; the CNF bound translates this algebraic reasoning into a combinatorial framework. The stretch is amplified by iteration in the sense of Krajíček and Razborov, along a tree as in Razborov's construction, and the hardness of WRank persists under iteration. The bamboo-tree result resolves the open problem of Alekhnovich, Ben-Sasson, Razborov and Wigderson and of Razborov on generators for $\mathrm{PCR}_{\mathbb F_2}$: previous generators used linear systems over $\mathbb F_2$, which $\mathrm{PCR}_{\mathbb F_2}$ refutes easily, or the weak pigeonhole principle, for which no $\mathrm{PCR}$ size lower bound with arbitrarily many pigeons is known. Because the bamboo-tree extension variables correspond to gates of a circuit, the function generator implies that $\mathrm{PCR}_{\mathbb F_2}$ has no short proofs of circuit lower bound statements such as $\mathrm{NP}\not\subseteq\mathrm{P}/\mathrm{poly}$.

## Depends on

- [The weak rank principle](weak-rank-principle.md)
- [Polynomial calculus resolution PCR_F](polynomial-calculus-resolution.md)

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 1, proof complexity generators and function generators; Section 2.1, Theorems 2.1 and 2.4; Section 5, the rank generator, stretching exactly when $n<m/2$; Theorems 5.7 and 5.20; Section 5.4, Definition 5.32 and Theorem 5.44 (iterated rank system), Definition 5.45, Definitions 5.48-5.49 and Theorem 5.51 (iterated bamboo-tree system)).
