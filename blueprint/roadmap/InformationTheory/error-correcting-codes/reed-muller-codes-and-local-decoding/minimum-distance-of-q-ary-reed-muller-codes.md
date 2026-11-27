# Minimum distance of q-ary Reed-Muller codes

Let $\mathbb{F}$ be a finite field with $q$ elements. The Reed-Muller code $\mathrm{RM}_q(m, d)$ is the set of evaluation tables $(P(x))_{x \in \mathbb{F}^m}$ of polynomials $P \in \mathbb{F}[X_1, \dots, X_m]$ of total degree at most $d$. Two distinct codewords differ on at least $(1 - d/q)\, q^m$ points. If $d < q$, the minimum distance of $\mathrm{RM}_q(m + 1, d)$ is exactly $(q - d)\, q^m$.

## Proof sketch

A nonzero polynomial of total degree at most $d$ vanishes on at most a $d/q$ fraction of $\mathbb{F}^m$ by the Schwartz-Zippel lemma, which gives the lower bound for the difference of two codewords. For $d < q$ the product $\prod_{j=1}^{d}(X_1 - t_j)$ over $d$ distinct field elements vanishes exactly on $d q^m$ points, so the bound is attained.

## Depends on

- [Linear code](../linear-codes/linear-code.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Sources

- I. S. Reed, "A Class of Multiple-Error-Correcting Codes and the Decoding Scheme", Transactions of the IRE Professional Group on Information Theory, 1954.
- D. E. Muller, "Application of Boolean Algebra to Switching Circuit Design and to Error Detection", Transactions of the IRE Professional Group on Electronic Computers, 1954.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
