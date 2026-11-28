# Recursive shape indices and the Yule second-moment recursion

**Yule splitting rule.** Let $P_Y$ be the Yule distribution on rooted binary trees with leaf set $\{1,\dots,n\}$. If $\emptyset\ne S_k\subsetneq\{1,\dots,n\}$ has $|S_k|=k$, $T_k$ is a tree on $S_k$ and $T'_{n-k}$ a tree on the complement, then the tree $T_k\,\widehat{\ }\,T'_{n-k}$ obtained by joining them at a new root has

$$P_Y\big(T_k\,\widehat{\ }\,T'_{n-k}\big)=\frac{2}{(n-1)\binom{n}{k}}\,P_Y(T_k)\,P_Y(T'_{n-k}).$$

**Recursive shape index.** A shape index $I$ is *recursive* if there is a symmetric function $f_I$ with

$$I\big(T_k\,\widehat{\ }\,T'_{n-k}\big)=I(T_k)+I(T'_{n-k})+f_I(k,n-k).$$

The Sackin index ($f_I(a,b)=a+b$), the Colless index ($f_I(a,b)=|a-b|$) and the total cophenetic index ($f_I(a,b)=\binom a2+\binom b2$) are recursive.

**Proposition (second-moment recursion).** If $I$ is recursive and $I_n$ denotes its value on a Yule tree with $n$ leaves, then for every $n\ge 2$

$$E_Y(I_n^2)=\frac{1}{n-1}\sum_{k=1}^{n-1}\Big(2E_Y(I_k^2)+4f_I(k,n-k)E_Y(I_k)+2E_Y(I_k)E_Y(I_{n-k})+f_I(k,n-k)^2\Big).$$

If moreover $E_Y(I_1)=0$, then with $\varepsilon_I(a,b-1)=f_I(a,b)-f_I(a,b-1)$ and $R_I(n-1)=E_Y(I_n)-E_Y(I_{n-1})$ this telescopes to a first-order recursion

$$E_Y(I_n^2)=\frac{n}{n-1}E_Y(I_{n-1}^2)+\frac{4}{n-1}\sum_{k=1}^{n-2}\varepsilon_I(k,n-1-k)E_Y(I_k)+\frac{4}{n-1}f_I(n-1,1)E_Y(I_{n-1})$$

$$\qquad+\frac{2}{n-1}\sum_{k=1}^{n-2}E_Y(I_k)R_I(n-k-1)+\frac{f_I(n-1,1)^2}{n-1}+\frac{1}{n-1}\sum_{k=1}^{n-2}\big(f_I(k,n-k)^2-f_I(k,n-k-1)^2\big).$$

## Expansion

The splitting rule says that under the Yule model the number $k$ of leaves on one side of the root is uniform on $\{1,\dots,n-1\}$ and, conditionally on $k$, the two subtrees are independent Yule trees on their leaf sets. Squaring the recursive definition, taking expectations and using independence gives the first identity; multiplying by $n-1$, writing the same identity for $n-1$ and subtracting gives the telescoped form. The recursion reduces exact variance computations for any recursive index to evaluating finite sums of its known means.

## Sources

- Gabriel Cardona, Arnau Mir, Francesc Rosselló, "Exact formulas for the variance of several balance indices under the Yule model", arXiv:1202.6573 (2012). Lemma 1 (Yule splitting rule), Lemma 3 and Corollary 1 (second-moment recursion), <https://doi.org/10.48550/arXiv.1202.6573>.
