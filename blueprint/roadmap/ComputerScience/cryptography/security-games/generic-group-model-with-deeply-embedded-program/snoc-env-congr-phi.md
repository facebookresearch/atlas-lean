# Environment extension commutes with relabeling

Let $\varphi : L \simeq L'$ be a bijection between label types, and let $\mathit{env}_1 : \{0, \dots, n-1\} \to L$ and $\mathit{env}_2 : \{0, \dots, n-1\} \to L'$ satisfy $\mathit{env}_2(i) = \varphi(\mathit{env}_1(i))$ for every $i$. If $x_2 = \varphi(x_1)$, then the [extended environments](snoc-env.md) satisfy, for every index $t \le n$,

$$
\mathrm{snoc}(\mathit{env}_2, x_2)(t) = \varphi\bigl(\mathrm{snoc}(\mathit{env}_1, x_1)(t)\bigr),
$$

where $\mathrm{snoc}(\mathit{env}, x)$ keeps $\mathit{env}$ at the indices below $n$ and has $x$ at index $n$.
