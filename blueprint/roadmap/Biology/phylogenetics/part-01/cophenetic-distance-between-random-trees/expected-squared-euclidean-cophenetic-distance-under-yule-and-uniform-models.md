# Expected squared Euclidean cophenetic distance under the Yule and uniform models

**Setting.** For a rooted binary phylogenetic tree $T$ on leaves $\{1,\dots,n\}$, the **cophenetic value** $\varphi_T(i,j)$ of two leaves $i \ne j$ is the depth (number of arcs from the root) of their lowest common ancestor, and $\varphi_T(i,i)$ is the depth of leaf $i$. The cophenetic vector $\varphi(T) = (\varphi_T(i,j))_{1\le i\le j\le n}$ determines $T$ up to isomorphism, and the **Euclidean cophenetic metric** is

$$d_{\varphi,2}(T_1,T_2) = \Bigl(\sum_{1\le i\le j\le n}\bigl(\varphi_{T_1}(i,j) - \varphi_{T_2}(i,j)\bigr)^2\Bigr)^{1/2}.$$

Let $D_n = d_{\varphi,2}(T_1,T_2)$ for two independent random trees with $n$ leaves drawn from the same model. In the **Yule** (equal-rate Markov) model, $P_Y(T) = \frac{2^{n-1}}{n!}\prod_{v \text{ internal}}\frac{1}{\ell_T(v)-1}$, where $\ell_T(v)$ is the number of leaves below $v$. In the **uniform** (PDA) model every tree has probability $1/(2n-3)!!$. Let $H_n = \sum_{k=1}^n 1/k$.

**Theorem.** For every $n \ge 2$,

$$\mathbb E_Y(D_n^2) = \frac{2n}{n-1}\Bigl(3n^2 - 10n - 1 + 8(n+1)H_n - 4(n+1)H_n^2\Bigr),$$

$$\mathbb E_U(D_n^2) = \frac13\bigl(4n^3 + 18n^2 - 10n\bigr) - \frac{n(n+3)}{2}\,\frac{(2n-2)!!}{(2n-3)!!} - \frac{n(n+7)}{4}\left(\frac{(2n-2)!!}{(2n-3)!!}\right)^2 .$$

For example, $\mathbb E_Y(D_4^2) \approx 9.41$ and $\mathbb E_U(D_4^2) = 10.56$. Asymptotically $\mathbb E_Y(D_n^2) \sim 6n^2$, while $\mathbb E_U(D_n^2) \sim (4/3 - \pi/4)\,n^3$, because $(2n-2)!!/(2n-3)!! \sim \sqrt{\pi n}$. The cubic growth reflects the depth of typical uniform trees, which is of order $\sqrt n$.

## Expansion

By independence and exchangeability of leaves,

$$\mathbb E(D_n^2) = 2\,\mathbb E\Bigl(\sum_{i\le j}\varphi_T(i,j)^2\Bigr) - \frac{2\,(\mathbb E S_n)^2}{n} - \frac{4\,(\mathbb E\Phi_n)^2}{n(n-1)},$$

where $S_n$ is the Sackin index (the sum of leaf depths, i.e. of the diagonal cophenetic values) and $\Phi_n$ the total cophenetic index (the sum of off-diagonal cophenetic values). The expectations of $S_n$ and $\Phi_n$ are classical. The new ingredient is $\mathbb E\bigl(\sum_{i\le j}\varphi_T(i,j)^2\bigr)$, which equals $5n(n-1) - 8n(H_n - 1)$ under Yule and $\frac16 n(4n^2+21n-7) - \frac34 n(n+3)\frac{(2n-2)!!}{(2n-3)!!}$ under the uniform model. Both come from recurrences obtained by splitting a tree at its root as $T_k \,\widehat{}\, T'_{n-k}$: every cophenetic value inside a subtree increases by one.

## Sources

- Gabriel Cardona, Arnau Mir, Francesc Rosselló, "The expected value of the squared euclidean cophenetic metric under the Yule and the uniform models", arXiv (2013). Section 2 (Yule and uniform models), Section 3: Theorems 2–3, Propositions 4–5. <https://doi.org/10.48550/arXiv.1301.5131>. Published version: Gabriel Cardona, Arnau Mir, Francesc Rosselló, Lucía Rotger, Mathematical Biosciences 295 (2018), 73–85, <https://doi.org/10.1016/j.mbs.2017.11.007>; locators above refer to the arXiv version.
