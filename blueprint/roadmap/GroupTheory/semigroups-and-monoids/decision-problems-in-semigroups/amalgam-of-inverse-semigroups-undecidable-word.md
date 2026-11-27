# Some amalgam of inverse semigroups with finite R-classes has undecidable word problem

The amalgamated free product of inverse semigroups $S_1$ and $S_2$ over a common inverse subsemigroup $U$ can have undecidable word problem even when $S_1$ and $S_2$ have finite $\mathcal{R}$-classes and the embeddings of $U$ are computable.

An amalgam of inverse semigroups $[S_1, S_2; U, \omega_1, \omega_2]$ consists of inverse semigroups $S_1$, $S_2$, $U$ and monomorphisms $\omega_i\colon U \to S_i$. If $S_i = \mathrm{Inv}\langle X_i \mid R_i \rangle$ with $X_1 \cap X_2 = \emptyset$, and $\lambda_i$ assigns to each element of $S_i$ a word representing it, the amalgamated free product in the category of inverse semigroups is

$$
S_1 *_U S_2 = \mathrm{Inv}\langle X_1 \cup X_2 \mid R_1 \cup R_2 \cup \{ (\lambda_1(\omega_1(u)), \lambda_2(\omega_2(u))) : u \in U \} \rangle .
$$

Two elements $a, b$ of an inverse semigroup are $\mathcal{R}$-related when they generate the same principal right ideal, equivalently $aa^{-1} = bb^{-1}$. There is an amalgam $[S_1, S_2; U, \omega_1, \omega_2]$ of inverse semigroups in which $S_1$ and $S_2$, and hence $U$, have finite $\mathcal{R}$-classes and $\omega_1$, $\omega_2$ are computable, such that the word problem of $S_1 *_U S_2$ with respect to the generating set $X_1 \cup X_2$ is undecidable (Theorems 1 and 4 of the source). In the construction $S_1$ and $S_2$ are given by finite inverse semigroup presentations.

This contrasts with amalgamated free products of finite inverse semigroups, whose word problem is decidable (Cherubini, Meakin and Piochi), and with Hall's theorem that every amalgam of inverse semigroups embeds in an inverse semigroup.

## Depends on

- [Inverse monoid and inverse semigroup presentations](inverse-monoid-and-semigroup-presentations.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof encodes a deterministic, reversible, alternating two-counter machine $\mathcal{M}$ in normalized form: $S_1$ and $S_2$ are "tape" inverse semigroups for the two counters, given by finite presentations with commuting, test, writing, erasing and finiteness relations, and the common subsemigroup $U$ carries the control states. For each pair $(m, n)$ of counter values there is a computable word $w_{m,n}$ with $w_{m,n} = 0$ in $S_1 *_U S_2$ exactly when $\mathcal{M}$ accepts $(m, n)$ (Theorem 3). Some normalized two-counter machine has undecidable acceptance problem (Corollary 1), which rests on the universality of reversible two-counter machines; so the word problem is undecidable. The same encoding shows that finiteness of a $\mathcal{D}$-class of such an amalgamated free product is undecidable even when $S_1$ and $S_2$ have finite $\mathcal{D}$-classes (Theorem 5).

## Sources

- E. Rodaro and P. V. Silva, "Amalgams of inverse semigroups and reversible two-counter machines", Journal of Pure and Applied Algebra 217 (2013), no. 4, 585–597, https://doi.org/10.1016/j.jpaa.2012.08.012; arXiv:1105.1905v1 (Theorem 1, Corollary 1, Theorem 3, Theorem 4 and Theorem 5 of arXiv:1105.1905v1; Theorem 1 in the introduction and Theorem 4 in Section 5 are the same statement).
