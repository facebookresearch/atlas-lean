# Weak rank lower bounds and generators for PCR over $\mathbb F_2$

For every $m>n$ and $A\in\mathbb F_2^{m\times m}$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of the algebraic or the bamboo-tree encoding of the weak rank principle has size $2^{\Omega(n)}$, so both are proof complexity generators stretching $2nm$ bits to $m^2$, and iterated variants are function generators with stretch $2^{n^{\Omega(1)}}$.

Polynomial calculus resolution $\mathrm{PCR}_{\mathbb F}$ refutes a polynomial system by deriving $1$ with the rules "from $f,g$ derive $\alpha f+\beta g$" and "from $f$ derive $x_i f$", after adding the Boolean axioms $x_i^2-x_i$, twin variables $\bar x_i$ with $1-x_i-\bar x_i$ and $\bar x_i^2-\bar x_i$; size is the number of distinct monomials in the refutation.

**Theorem (algebraic encoding).** For every $m>n$ and $A\in\mathbb F_2^{m\times m}$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of $\mathrm{Rank}^m_n(A)$ requires size $2^{\Omega(n)}$. Consequently $\mathrm{Rank}^m_n(A)$ is a proof complexity generator stretching $2nm$ bits into $m^2$. Moreover, the iterated variant of $\mathrm{Rank}^m_n(A)$ is a function generator with stretch $2^{n^{\Omega(1)}}$.

**Theorem (bamboo-tree encoding).** For every $m>n$ and $A\in\mathbb F_2^{m\times m}$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of $\mathrm{BTRank}^m_n(A)$ requires size $2^{\Omega(n)}$. Consequently $\mathrm{BTRank}^m_n(A)$ is a proof complexity generator stretching $2nm$ bits into $m^2$ bits, and there is an iterated variant of $\mathrm{BTRank}^m_n(A)$ that yields a function generator with stretch $2^{n^{\Omega(1)}}$.

Here the encodings are those of the [weak rank principle](weak-rank-principle.md); a refutation exists only when the system is unsatisfiable, for instance when $A$ has rank greater than $n$.

## Expansion

The algebraic bound uses random restrictions to reduce size to degree, then a degree lower bound for the restricted rank system; the CNF bound translates this algebraic reasoning into a combinatorial framework. The stretch is amplified by iteration in the sense of Krajíček and Razborov, and the hardness of WRank persists under iteration. The bamboo-tree result resolves the open problem of Alekhnovich, Ben-Sasson, Razborov and Wigderson and of Razborov on generators for $\mathrm{PCR}_{\mathbb F_2}$: previous generators used linear systems over $\mathbb F_2$, which $\mathrm{PCR}_{\mathbb F_2}$ refutes easily, or the weak pigeonhole principle, for which no $\mathrm{PCR}$ size lower bound with arbitrarily many pigeons is known. Because the bamboo-tree extension variables correspond to gates of a circuit, the function generator implies that $\mathrm{PCR}_{\mathbb F_2}$ has no short proofs of circuit lower bound statements such as $\mathrm{NP}\not\subseteq\mathrm{P}/\mathrm{poly}$.

## Depends on

- [The weak rank principle](weak-rank-principle.md)

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 2.1, Theorems 2.1 and 2.4; Preliminaries, definition of PCR).
