# Rooted versus unrooted cherry and pitchfork statistics

Let $B_n,A_n$ be the numbers of cherries and pitchforks of a random unrooted binary tree with $n$ leaves, and $B_n^*,A_n^*$ those of a random rooted binary tree with $n$ leaves, under the same model (PDA, uniform; or YHK, Yule–Harding–Kingman).

**Theorem (means).** For $n\ge6$ and $Y\in\{A,B\}$,

$$\mathbb{E}_{\mathrm{YHK}}(Y_n^*)<\mathbb{E}_{\mathrm{YHK}}(Y_n)\le \mathbb{E}_{\mathrm{YHK}}(Y_n^*)+\tfrac35,\qquad \mathbb{E}_{\mathrm{PDA}}(Y_n^*)+\tfrac14<\mathbb{E}_{\mathrm{PDA}}(Y_n)\le\mathbb{E}_{\mathrm{PDA}}(Y_n^*)+\tfrac{16}{21}.$$

The gap $\mathbb{E}(Y_n)-\mathbb{E}(Y_n^*)$ decreases strictly in $n$, with limit $0$ under YHK and $\tfrac14$ under PDA. Also $\mathbb{E}_{\mathrm{PDA}}(Y_n)<\mathbb{E}_{\mathrm{YHK}}(Y_n)<\tfrac43\mathbb{E}_{\mathrm{PDA}}(Y_n)$ for $Y_n\in\{A_n^*,B_n^*,B_n\}$ and $n\ge6$, and $\mathbb{E}(A_n)\sim\tfrac12\mathbb{E}(B_n)$ under both models.

**Theorem (variances).** For $n\ge7$, $\operatorname{Var}(Y_n^*)>\operatorname{Var}(Y_n)$ under both models, and for $n\ge6$, $\operatorname{Cov}(A_n^*,B_n^*)>\operatorname{Cov}(A_n,B_n)$.

**Theorem (total variation).** Under PDA, for $n\ge4$, with $\Delta(n)=\lfloor n/4\rfloor$,

$$d_{TV}(B_n^*,B_n)=\frac{n!\,(n-2)!\,(n-4)!\,2^{\,n-2\Delta(n)-1}}{(2n-3)!\,(n-2\Delta(n)-2)!\,\Delta(n)!\,(\Delta(n)-1)!}=\frac{1+o(1)}{\sqrt{2\pi n}}.$$

Under YHK the sequence $d_{TV}(B_n^*,B_n)$, $n\ge4$, is strictly decreasing.

So rooted and unrooted cherry laws merge in total variation, but under the uniform model the unrooted mean stays $\tfrac14$ above the rooted mean, and unrooted counts are less variable.

## Depends on

- [Exact cherry distribution of unrooted PDA trees](exact-cherry-distribution-of-unrooted-pda-trees.md)

## Expansion

The rooted PDA cherry mean is $n(n-1)/(2(2n-3))=n/4+1/8+O(1/n)$ while the unrooted mean is $n(n-1)/(2(2n-5))=n/4+3/8+O(1/n)$, which gives the limiting gap $\tfrac14$: unrooting a tree whose root has a leaf child can merge that leaf into a new cherry. Under YHK both means are $n/3+O(n^{-2})$. Comparing the two closed-form PDA probability mass functions shows that their ratio is monotone in $k$, so the total variation distance is a single partial sum up to the crossing point $\Delta(n)$, and Stirling's formula gives the $1/\sqrt{2\pi n}$ rate.

## Sources

- K. P. Choi, A. Thompson, T. Wu, "On cherry and pitchfork distributions of random rooted and unrooted phylogenetic trees", arXiv:2002.12643 (2020), Section 5, Propositions 5–8 and Theorem 9, <https://doi.org/10.48550/arXiv.2002.12643>.
