---
article_id: af_ea83fb47e0fb0c8eb785bfeb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SpectralTheorem.spectral_theorem
---

# Theorem (Spectral Theorem)

Given a Hermitian space $V$, for any normal linear operator $T$, there exists an orthonormal eigenbasis of $V$: $\{u_1, \cdots, u_n\}.$ In matrix form, for any normal matrix $M \in GL_n(\mathbb{C}),$ there exists a unitary matrix $P$ such that $P^{-1} M P$ is diagonal. The real version states that for a Euclidean vector space $V$ and a symmetric linear operator $T$, there exists an orthonormal eigenbasis; equivalently, for any symmetric matrix $M \in GL_n(\mathbb{R})$, there exists an orthogonal matrix $P$ such that $P^{-1}MP$ is diagonal. All eigenvalues of real symmetric matrices are real.

## Depends on

- [Definition (Section: Euclidean and Hermitian Spaces, Subsection: Complex Linear Operators)](../euclidean-and-hermitian-spaces/060-definition.md)

## Proof depends on

- [Lemma 1](067-lemma-1.md)
- [Lemma 2](069-lemma-2.md)

## Sources

- [MIT RES.18-011 Algebra I Student Notes (Fall 2021), Section: The Spectral Theorem, Subsection: The Spectral Theorem](../../../../../sources/v1/AlgebraNotes.md)
