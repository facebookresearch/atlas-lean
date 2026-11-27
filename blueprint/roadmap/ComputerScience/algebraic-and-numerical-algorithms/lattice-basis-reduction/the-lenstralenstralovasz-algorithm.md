# The Lenstra–Lenstra–Lovász algorithm

Let $b_1, \dots, b_n$ be a basis of a lattice $L \subseteq \mathbb{Z}^n$ and $\delta \in (1/4, 1)$. For fixed $\delta$, the LLL algorithm terminates after a number of iterations polynomial in $n$ and in the logarithm of the largest basis norm (the bound grows like $1/\log(1/\delta)$ as $\delta \to 1$), and outputs a $\delta$-reduced basis $b'_1, \dots, b'_n$ of $L$: size-reduced, with $\delta \|b^*_i\|^2 \le \|b^*_{i+1} + \mu_{i+1,i} b^*_i\|^2$ for the Gram–Schmidt vectors $b^*_i$. Its first vector satisfies $\|b'_1\| \le \bigl(2/\sqrt{4\delta - 1}\bigr)^{n-1} \lambda_1(L)$, where $\lambda_1(L)$ is the length of a shortest nonzero vector; for $\delta = 3/4$ this is $2^{(n-1)/2}\lambda_1(L)$.

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring polynomials with rational coefficients", *Mathematische Annalen* 261(4):515–534, 1982
