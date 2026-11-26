# Kernels lemma

Let $R$ be a commutative ring, $M$ an $R$-module, $f$ an $R$-linear endomorphism of $M$, and $(p_i)_{i \in \iota}$ a finite family of pairwise coprime polynomials in $R[X]$: for all $i \ne j$ there are $a, b \in R[X]$ with $a p_i + b p_j = 1$. Then the submodules $\ker p_i(f)$ are independent, and their sum is $\ker \bigl(\prod_i p_i\bigr)(f)$.

## Idea

If $ap + bq = 1$, then $x = a(f)p(f)x + b(f)q(f)x$ for every $x$. When $x$ is killed by $(pq)(f)$, the first term is killed by $q(f)$ and the second by $p(f)$, so $x$ splits into a part in $\ker q(f)$ and a part in $\ker p(f)$, and the same identity shows that the two kernels meet only in $0$. Induction gives the case of several polynomials. Applied to the factorization of a polynomial that annihilates $f$, for instance its characteristic polynomial by Cayley–Hamilton, the lemma decomposes the whole space into $f$-invariant pieces: this is the primary decomposition behind diagonalization and the Jordan form.

## Statements

- [Kernels lemma](kernels-lemma-pairwise-is-coprime.md)
- [Independence and sum of kernels of pairwise coprime polynomials](i-sup-indep-ker-aeval-and-i-sup-eq-of-pa.md): the same statement, independence and sum together, as the declaration the main statement is derived from
- [Kernel of a product of pairwise coprime polynomials](i-sup-ker-aeval-eq-ker-aeval-prod-of-pai.md): the sum of the kernels is the kernel of the product
- [Kernels of pairwise coprime polynomials are independent over a finite set](sup-indep-ker-aeval-of-pairwise-is-copri.md): independence of the kernels
