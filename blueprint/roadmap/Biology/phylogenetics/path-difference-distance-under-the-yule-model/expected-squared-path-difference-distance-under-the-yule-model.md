# Expected squared path-difference distance under the Yule model

**Setting.** Let $\mathcal{BT}_n$ be the set of rooted binary phylogenetic trees with leaves $\{1,\dots,n\}$, and $d_T(i,j)$ the number of edges on the path between leaves $i,j$ of $T$. The *path-difference distance* (Farris) is

$$
d_\nu(T,T')=\Big(\sum_{1\le i<j\le n}\big(d_T(i,j)-d_{T'}(i,j)\big)^2\Big)^{1/2}.
$$

Under the *Yule* (equal-rate Markov) model a tree grows by splitting a uniformly chosen leaf, then labels are assigned uniformly; equivalently $P_Y(T)=\frac{2^{n-1}}{n!}\prod_{v}\frac1{\ell_T(v)-1}$ over internal nodes $v$, where $\ell_T(v)$ is the number of leaves below $v$. Let $H_n=\sum_{i\le n}1/i$ and $H^{(2)}_n=\sum_{i\le n}1/i^2$. For a random $T$ put $D_n=\sum_{i<j}d_T(i,j)$ and $D_n^{(2)}=\sum_{i<j}d_T(i,j)^2$, and let $N_n^2=d_\nu(T,T')^2$ for independent Yule trees $T,T'$.

**Theorem.**

1. *(Reduction.)* $\displaystyle E_Y(N_n^2)=2\Big(E_Y(D^{(2)}_n)-\frac{E_Y(D_n)^2}{\binom n2}\Big).$
2. *(Moments of leaf distances.)* $E_Y(D_n)=2n(n+1)H_n-4n^2$ and

$$
E_Y(D^{(2)}_n)=8n(n+1)\big(H_n^2-H_n^{(2)}\big)-2n(15n+7)H_n+45n^2-n .
$$

3. *(Main formula.)* For $n\ge2$,

$$
E_Y(N_n^2)=\frac{2n}{n-1}\Big(2(n^2+24n+7)H_n+13n^2-46n+1-16(n+1)H_n^2-8(n^2-1)H_n^{(2)}\Big).
$$

## Expansion

Expanding the square and using independence of $T,T'$ gives, pair by pair, $2E[d_T(i,j)^2]-2E[d_T(i,j)]^2$; exchangeability of leaf labels under the Yule model makes $E[d_T(i,j)]=E_Y(D_n)/\binom n2$ for every pair, which yields the reduction. $E_Y(D^{(2)}_n)$ is computed by recursion on the root split: writing $T=T_1\,\widehat{}\,T_2$ with $|T_1|=k$ (uniform on $1,\dots,n-1$ under Yule), $D^{(2)}(T)$ decomposes into $D^{(2)}(T_1)+D^{(2)}(T_2)$ plus cross terms in the depth sums $S(T_i)$ and squared-depth sums $S^{(2)}(T_i)$ and $4k(n-k)$; the resulting recurrences are solved with harmonic-sum identities such as $\sum_{k<n}H_k/(k+1)=\tfrac12(H_n^2-H_n^{(2)})$. As a check, the formula gives $E_Y(N_2^2)=0$ (one tree) and grows like $E_Y(N_n^2)\sim4n^2\ln n$, which calibrates whether two observed trees are closer than random Yule trees.

## Sources

- Gabriel Cardona, Arnau Mir, Francesc Rosselló, "The expected value under the Yule model of the squared path-difference distance", arXiv:1203.2503 (2012), Section 3: Theorem 1, Proposition 2, Theorem 3; Appendix (recursions and harmonic-sum lemmas), <https://doi.org/10.48550/arXiv.1203.2503>.
