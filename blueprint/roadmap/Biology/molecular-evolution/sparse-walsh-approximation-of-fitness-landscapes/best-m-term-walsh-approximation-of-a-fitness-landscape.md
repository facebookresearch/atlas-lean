# Best m-term Walsh approximation of a fitness landscape

**Setting.** Consider $L$ biallelic loci, the genotypes $g \in \{0,1\}^L$ and a fitness landscape $W : \{0,1\}^L \to \mathbb{R}$. Identify $h \in \{0,1\}^L$ with its support $S_h = \{i : h_i = 1\}$. The *epistatic (Walsh) coefficient* of $W$ at $h$, which measures the interaction among the loci in $S_h$ (order $|S_h|$), is the [Walsh–Fourier coefficient](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-fourier-coeff.md)

$$E_W(h) = \hat W(S_h) = 2^{-L} \sum_{g \in \{0,1\}^L} (-1)^{g \cdot h}\, W(g),$$

so that $W(g) = \sum_h (-1)^{g \cdot h} E_W(h)$; in vector form $\vec E_W = 2^{-L}\Psi \vec W$ with the Sylvester–Hadamard matrix $\Psi_{g,h} = (-1)^{g \cdot h}$. A *subsetting approximation* with $m$ terms ($0 \le m \le 2^L$) keeps a set $K$ of $m$ indices $h$ and discards the others:

$$W^{(K)}(g) = \sum_{h \in K} (-1)^{g \cdot h} E_W(h).$$

**Theorem.** Among all subsetting approximations with $m$ terms, the sum of squares $\sum_g \big(W(g) - W^{(K)}(g)\big)^2$ is minimized exactly by the sets $K$ consisting of $m$ indices whose coefficients $E_W(h)$ are largest in absolute value. The minimum equals $2^L$ times the sum of squares of the discarded coefficients.

In particular, truncating a landscape to all interactions of order at most $k$ is least-squares optimal only if those are the largest coefficients; dropping a large higher-order coefficient can change the landscape's peaks and sign-epistasis structure.

## Depends on

- [Fourier–Walsh coefficient under the uniform measure](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-fourier-coeff.md)

## Proof depends on

- [Parseval's identity on the Boolean cube](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-parseval.md)

## Expansion

The difference $f = W - W^{(K)}$ has Walsh coefficient $E_W(h)$ at $S_h$ for $h \notin K$ and $0$ for $h \in K$. Parseval's identity with $g = f$ gives $2^{-L} \sum_g f(g)^2 = \mathbb{E}[f^2] = \sum_{h \notin K} E_W(h)^2$, so $\sum_g \big(W(g) - W^{(K)}(g)\big)^2 = 2^L \sum_{h \notin K} E_W(h)^2$. This is smallest when the $2^L - m$ discarded coefficients are those of smallest absolute value; the sign of a coefficient plays no role.

## Sources

- D. M. Weinreich, Y. Lan, J. Jaffe and R. B. Heckendorn, "The Influence of Higher-Order Epistasis on Biological Fitness Landscape Topography", *Journal of Statistical Physics* (2018), Sect. 2.2 (Eq. 1), Sect. 2.3 (subsetting approximations) and Appendix, Theorems 1 and 2. <https://doi.org/10.1007/s10955-018-1975-3> (PMC5986866)
