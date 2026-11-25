# Rows of $R_\alpha$ against falling factorials

For a sequence $\alpha \colon \mathbb{N} \to \mathbb{Q}$ let $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$ and $\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, where $m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial. For natural numbers $k, m$ let $R_{k,m} = \frac{(-1)^{m-k}}{(m-k)!} \Psi_\alpha(k)$ if $k \le m$ and $R_{k,m} = 0$ if $k > m$. Then for all natural numbers $k$ and $j$,

$$\sum_{m=1}^{j} R_{k,m} \, (j-1)^{\underline{m-1}} = \begin{cases} \Omega(\alpha, j) & \text{if } k = j, \\ 0 & \text{otherwise.} \end{cases}$$

No nonvanishing hypothesis on $\Omega$ is needed.
