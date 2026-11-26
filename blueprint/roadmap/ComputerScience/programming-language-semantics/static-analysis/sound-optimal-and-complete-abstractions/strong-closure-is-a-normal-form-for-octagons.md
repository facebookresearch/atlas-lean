# Strong closure is a normal form for octagons

With the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md), work over a numerical set $\mathbb{I} \ne \mathbb{Z}$, and let $m^+$ be a coherent DBM over the $2N$ forms. It is *strongly closed* if it is coherent, it is closed ($m^+_{ii} = 0$ and $m^+_{ij} \le m^+_{ik} + m^+_{kj}$ for all $i, j, k$), and $m^+_{ij} \le (m^+_{i\bar\imath} + m^+_{\bar\jmath j})/2$ for all $i, j$. The *strong closure* $(m^+)^\bullet = m^+_N$ is computed by $N$ rounds $m^+_0 = m^+$, $m^+_{k+1} = S^+(C^+_{2k}(m^+_k))$ for $0 \le k < N$, in time $O(N^3)$, where the closure step through both forms of $v_k$ is $[C^+_{2k}(n)]_{ii} = 0$ and, for $i \ne j$,

$$[C^+_{2k}(n)]_{ij} = \min\bigl(n_{ij},\ n_{i,2k} + n_{2k,j},\ n_{i,2k+1} + n_{2k+1,j},\ n_{i,2k} + n_{2k,2k+1} + n_{2k+1,j},\ n_{i,2k+1} + n_{2k+1,2k} + n_{2k,j}\bigr)$$

and the tightening is $[S^+(n)]_{ij} = \min(n_{ij}, (n_{i\bar\imath} + n_{\bar\jmath j})/2)$. The diagonal clause matters: for one variable and the matrix with every entry $+\infty$, the minimum alone changes nothing, although zeros on the diagonal give a smaller matrix with the same octagon. Ordinary shortest-path closure does not suffice: from $v_0^+ - v_0^- \le 2$ and $v_1^+ - v_1^- \le 4$, that is $x \le 1$ and $y \le 2$, only the tightening derives $v_0^+ - v_1^- \le 3$, that is $x + y \le 3$.

For a coherent $m^+$ whose octagon is nonempty:
1. $m^+ = (m^+)^\bullet$ if and only if $m^+$ is strongly closed.
2. **Saturation.** For all $i, j$ with $(m^+)^\bullet_{ij} \ne +\infty$ there is $s \in D(m^+)$ with $s_{2k} = -s_{2k+1}$ for all $k$ and $s_j - s_i = (m^+)^\bullet_{ij}$.
3. **Normal form.** $(m^+)^\bullet$ is the least coherent DBM, for the pointwise order, among those with the same octagon as $m^+$.
4. **Inclusion and equality.** For coherent $m^+$ and $n^+$ with nonempty octagons, $D^+(m^+) \subseteq D^+(n^+)$ if and only if $(m^+)^\bullet \trianglelefteq n^+$, and $D^+(m^+) = D^+(n^+)$ if and only if $(m^+)^\bullet = (n^+)^\bullet$.

Over $\mathbb{Z}$ the strong closure is not the least representation: from $2x \le 2c + 1$ for an integer $x$ it does not derive $2x \le 2c$, so the integer case needs an additional tightening of such bounds.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)

## Sources

- A. Miné, "The octagon abstract domain", *Proceedings of the Eighth Working Conference on Reverse Engineering (WCRE 2001)*, IEEE, 2001, pp. 310–319, doi:10.1109/WCRE.2001.957836, author copy <https://arxiv.org/abs/cs/0703084>: Section V.C (Definition 1 of strongly closed DBMs, the strong closure algorithm of Figure 8 and its $O(N^3)$ cost, and Theorem 4 for $\mathbb{I} \ne \mathbb{Z}$), Section V.D (the failure over $\mathbb{Z}$) and Section VI.A (Theorem 5, equality and inclusion testing).
