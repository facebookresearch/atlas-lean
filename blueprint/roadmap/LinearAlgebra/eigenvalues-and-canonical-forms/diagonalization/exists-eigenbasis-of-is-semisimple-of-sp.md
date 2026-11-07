# Eigenbasis of a semisimple endomorphism with split characteristic polynomial

Let $V$ be a
finite-dimensional vector space over a field $K$ and let $f$ be a semisimple endomorphism of $V$
(every $f$-invariant subspace has an $f$-invariant complement) whose characteristic polynomial
splits over $K$. Then for every finite type $\iota$ with exactly $\dim_K V$ elements there are a
basis $(b_i)_{i \in \iota}$ of $V$ and scalars $(\mu_i)_{i \in \iota}$ in $K$ such that each $b_i$
is an eigenvector of $f$ with eigenvalue $\mu_i$.

Proof: The minimal polynomial is squarefree and splits, so it is a product of distinct factors
$X - \mu$. The kernels lemma for these factors, proved by induction from the two-factor case,
shows that the eigenspaces span $V$, and bases of the eigenspaces are collected and reindexed.
This is the diagonalizability criterion derived from the kernels lemma in the French Wikipedia
article *Lemme des noyaux*, <https://fr.wikipedia.org/wiki/Lemme_des_noyaux>.

## Sources

- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / diagonalization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 1.3.12.
