# Random output restrictions of a demi-bits generator are proof complexity generators

For every proof system that cannot be hurt by extra axioms, keeping a random set of $m$ output bits of a demi-bits generator against it gives, with probability at least $1-4m\log(1/\varepsilon)/N$ (constant probability in the stated parameter range), a proof complexity generator against it. No extra circuitry is added, so generators in $\mathsf{NC}^0$ stay in $\mathsf{NC}^0$.

**Well-behaved proof systems.** A proof system $\mathcal P$ is well-behaved if there is a polynomial $p$ such that for all CNFs $C\subseteq C'$ (every clause of $C$ is a clause of $C'$), a length-$\ell$ $\mathcal P$-refutation of $C$ implies a length-$\mathrm{poly}(\ell)$ $\mathcal P$-refutation of $C'$.

**Restrictions and encodings.** For $G:\{0,1\}^n\to\{0,1\}^N$ and $I=\{i_1<\dots<i_m\}\subseteq[N]$, let $G|_I(x)=G(x)_{i_1}\cdots G(x)_{i_m}$. Write "$y\notin\mathrm{Range}(G)$" for a CNF encoding of the statement that no $z\in\{0,1\}^n$ has $G(z)=y$, chosen so that every clause of "$y|_I\notin\mathrm{Range}(G|_I)$" is also a clause of "$y\notin\mathrm{Range}(G)$" (the gate-by-gate encoding $\tau_y(G)$ has this property). $G$ is a proof complexity generator against $\mathcal P$-proofs of length $\ell$ if for every $y$ no such proof of "$y\notin\mathrm{Range}(G)$" exists.

**Theorem.** Let $\mathcal P$ be a well-behaved proof system. Then there is a polynomial $p$ such that the following holds. Let $2^{-o(N)}<\varepsilon\le 1/2$, let $n<m<N/(10\log(1/\varepsilon))$, and let $G:\{0,1\}^n\to\{0,1\}^N$ be a $(1-\varepsilon)$-secure demi-bits generator against $\mathcal P$-proofs of length $p(\ell)$, so that at least $\varepsilon 2^N$ strings $y$ have no such proof of "$y\notin\mathrm{Range}(G)$". Then with probability at least

$$
1-\frac{4m\log(1/\varepsilon)}{N}
$$

over a uniformly random $I\subseteq[N]$ with $|I|=m$, the restriction $G|_I$ is a proof complexity generator secure against $\mathcal P$-proofs of length $\ell$.

The paper's informal Theorem 1.8 states the idea for an unrestricted index set at output length $10n$: for a demi-bits generator $G:\{0,1\}^n\to\{0,1\}^{10n}$ against a well-behaved $\mathcal P$, with constant probability over a uniformly random subset $I\subseteq[10n]$ of unrestricted size, $G|_I$ is a proof complexity generator against $\mathcal P$ (and $|I|>n$ with high probability). It is not a special case of the fixed-size theorem above, whose parameters force $|I|=m<N/(10\log(1/\varepsilon))$.

## Expansion

Let $\mathrm{Hard}\subseteq\{0,1\}^N$ be the strings $y$ for which "$y\notin\mathrm{Range}(G)$" has no $\mathcal P$-proof of length $p(\ell)$, so $|\mathrm{Hard}|\ge\varepsilon 2^N$. A set $H$ shatters $I$ if every pattern in $\{0,1\}^I$ is $y|_I$ for some $y\in H$. Pajor's lemma says $H$ shatters at least $|H|$ index sets; with the Kruskal-Katona theorem this shows that a uniformly random projection onto $m\le 0.4N$ coordinates is an $(N-\Delta,4m\Delta/N)$ zero-error disperser family when $\Delta\le o(N)$, so $\mathrm{Hard}$ shatters a random $I$ of size $m$ with the stated probability. If $\mathrm{Hard}$ shatters $I$ and some $y'\in\{0,1\}^I$ had a short proof of "$y'\notin\mathrm{Range}(G|_I)$", pick $y\in\mathrm{Hard}$ with $y|_I=y'$; the clauses of the restricted formula are among those of "$y\notin\mathrm{Range}(G)$", and well-behavedness gives a length-$p(\ell)$ proof for $y$, a contradiction.

Unlike the extractor-based transformation, which needs closure under simple parity reductions, this applies to resolution and other weak systems. As a corollary, for well-behaved $\mathcal P$, constants $k\ge 2$, and $\ell(n)>n$: for every constant $c\ge 1$ there is an $\mathsf{NC}^0_k$ demi-bits generator $\{0,1\}^n\to\{0,1\}^{c\ell(n)}$ that is $0.99$-secure against $\mathcal P$, if and only if for every constant $c\ge 1$ there is an $\mathsf{NC}^0_k$ proof complexity generator of the same stretch secure against $\mathcal P$. The same disperser framework shows that, for a universal constant $c\ge 1$, if a demi-bits generator with stretch $c\ell(n)$ is computable in $\mathsf{NC}^0_k$, then range avoidance for $\mathsf{NC}^0_k$ circuits of stretch $n\to\ell(n)$ is not in $\mathsf{SearchNP}$.

## Depends on

- [Demi-bits generators](demi-bits-generator.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Xin Li, Hanlin Ren, Yan Zhong, "Many Proof Complexity Generators Inside One Demi-Bits Generator", *FOCS* 2026, arXiv:2609.23228v1, https://arxiv.org/abs/2609.23228 (Theorem 4.12, Definition 4.10, Fact 4.11, Theorem 1.8, Theorem 3.3, Lemma 2.9, Corollaries 1.9 and 4.14, Remark 4.13).
