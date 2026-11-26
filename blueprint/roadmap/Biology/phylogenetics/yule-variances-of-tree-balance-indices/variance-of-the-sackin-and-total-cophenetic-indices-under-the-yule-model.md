# Variance of the Sackin and total cophenetic indices under the Yule model

**Setting.** Let $\mathcal T_n$ be the set of rooted binary phylogenetic trees on the leaf set $\{1,\dots,n\}$, and let $T_n$ be drawn from the Yule (pure-birth, equal-rates Markov) distribution $P_Y$ on $\mathcal T_n$. For $T\in\mathcal T_n$ define

- the **Sackin index** $S(T)=\sum_{\ell}\delta_T(\ell)$, the sum over leaves of their depths (number of edges from the root);
- the **total cophenetic index** $\Phi(T)=\sum_{1\le i<j\le n}\varphi_T(i,j)$, where $\varphi_T(i,j)$ is the depth of the lowest common ancestor of leaves $i$ and $j$.

Write $H_n=\sum_{k=1}^n 1/k$ and $H_n^{(2)}=\sum_{k=1}^n 1/k^2$, and let $S_n=S(T_n)$, $\Phi_n=\Phi(T_n)$.

**Theorem (exact Yule variances).** For every $n\ge 1$,

$$\sigma_Y^2(S_n)=7n^2-4n^2H_n^{(2)}-2nH_n-n,$$

$$\sigma_Y^2(\Phi_n)=\frac{1}{12}\left(n^4-10n^3+131n^2-2n\right)-4n^2H_n^{(2)}-6nH_n,$$

and the covariance of the two indices is

$$\operatorname{Cov}_Y(S_n,\Phi_n)=4n\left(nH_n^{(2)}+H_n\right)+\frac{1}{6}n\left(n^2-51n+2\right).$$

For the combined index $\overline\Phi=S+\Phi$ the formulas collapse to $E_Y(\overline\Phi_n)=n(n-1)$ and

$$\sigma_Y^2(\overline\Phi_n)=2\binom{n}{4}.$$

(The means used are $E_Y(S_n)=2n(H_n-1)$ and $E_Y(\Phi_n)=n(n-1)-2n(H_n-1)$.)

**Asymptotics.** As $n\to\infty$, with $\gamma$ Euler's constant,

$$\sigma_Y^2(S_n)=\Big(7-\frac{2\pi^2}{3}\Big)n^2+n\big(3-2\ln n-2\gamma\big)-3+O(1/n),$$

$$\sigma_Y^2(\Phi_n)=\frac{n^4}{12}-\frac{5}{6}n^3+\Big(\frac{131}{12}-\frac{2\pi^2}{3}\Big)n^2-6n\ln n+\Big(\frac{23}{6}-6\gamma\Big)n-5+O(1/n).$$

So the Sackin index has standard deviation of order $n$, while the cophenetic index has standard deviation of order $n^2$.

## Depends on

- [Recursive shape indices and the Yule second-moment recursion](recursive-shape-indices-and-the-yule-second-moment-recursion.md)

## Expansion

Both indices are recursive: for $T=T_k\,\widehat{\ }\,T'_{n-k}$ (root splitting into subtrees with $k$ and $n-k$ leaves), $S(T)=S(T_k)+S(T'_{n-k})+n$ and $\Phi(T)=\Phi(T_k)+\Phi(T'_{n-k})+\binom{k}{2}+\binom{n-k}{2}$. Under the Yule model the root split size is uniform on $\{1,\dots,n-1\}$ and the two subtrees are independent Yule trees, which yields a linear recursion for the second moment. Solving it uses closed forms for sums of harmonic numbers such as $\sum_{k=1}^{n-1}H_k^2=nH_n^2-(2n+1)H_n+2n$ and $\sum_{k=1}^{n-1}H_k/(k+1)=\tfrac12(H_n^2-H_n^{(2)})$. Subtracting the squared known means gives the variances; the asymptotics follow from $H_n=\ln n+\gamma+\tfrac{1}{2n}+O(n^{-2})$ and $H_n^{(2)}=\pi^2/6-1/n+O(n^{-2})$. The variance formula for $\Phi$ in the paper's introduction contains a typo; the corollary version stated here agrees with exact enumeration of the Yule recursion for small $n$. Exact variances are what is needed to standardize these statistics in tests of the Yule null model for trees of any size.

## Sources

- Gabriel Cardona, Arnau Mir, Francesc Rosselló, "Exact formulas for the variance of several balance indices under the Yule model", arXiv:1202.6573 (2012). Theorem 1 and Corollaries 2–3 (Sackin), Theorem 2 and Corollaries 4–5 (total cophenetic), Theorem 3 and Corollary 6 ($S+\Phi$), Corollaries 9 and 11 (covariances), <https://doi.org/10.48550/arXiv.1202.6573>.
