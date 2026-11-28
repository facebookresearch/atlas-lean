# Weak ergodicity of age structures under time-varying rates

Let $x_1, x_2, \dots$ be operators representing time-varying vital rates (for example Leslie matrices), chosen from a set $X$, and let $y_n = x_n \cdots x_1 y_0$, normalized to sum to $1$, be the age structure at time $n$. In classical stable population theory $x_n = x_1$ for all $n$ and $y_n$ approaches the stable age distribution determined by $x_1$, not by $y_0$. In the weak ergodic theorem of demography, due to López, the sequence $(x_n)$ is an arbitrary determinate sequence from $X$, and for suitable $X$ the age structure $y_n$ approaches a possibly time-varying sequence that depends on $(x_n)$ and not on $y_0$: for every $\delta > 0$ there is $m_0$ such that $d(x_m \cdots x_1 y, x_m \cdots x_1 y') < \delta$ for all $m \ge m_0$, all initial structures $y, y'$ and all sequences from $X$ (Cohen 1977, Introduction and Theorem 2). Golubitsky, Keeler and Rothschild (1975) prove the theorem by the projective method; Cohen (1977) uses it to obtain ergodicity of age structure when the vital rates follow a Markov chain.

## Expansion

1. The model: products of nonnegative matrices, normalization, and the uniform weak ergodicity property.
2. A precise sufficient condition (Seneta 2006, Theorem 3.3): there are an integer $r_0 \ge 1$ and $\gamma > 0$ such that every product of $r_0$ consecutive matrices of the sequence is positive and in every matrix of the sequence the smallest positive entry is at least $\gamma$ times the largest entry; then the forward products are weakly ergodic at a geometric rate.
3. Hilbert's projective metric on the positive cone and Birkhoff's contraction coefficient for positive matrices, and the contraction of $r_0$-step products under the condition of item 2.
4. From convergence to $0$ of the projective distance to weak ergodicity in the norm of normalized vectors.
5. Strong ergodicity (convergence of $y_n$ itself when $x_n \to x$), as a separate statement.

## Sources

- J. E. Cohen, Ergodicity of age structure in populations with Markovian vital rates. II. General states, Adv. Appl. Probab. 9 (1977), 18–37, Introduction, Theorem 2 and Section 2.5 (proof of Corollary 1). <https://doi.org/10.2307/1425814>
- E. Seneta, *Non-negative Matrices and Markov Chains*, revised printing, Springer, New York, 2006, Section 3.2, Theorem 3.3.
- Original result: M. Golubitsky, E. B. Keeler and M. Rothschild, Convergence of the age structure: applications of the projective metric, Theor. Popul. Biol. 7 (1975), 84–93. <https://doi.org/10.1016/0040-5809(75)90007-6> The weak ergodic theorem and its projective proof follow Cohen (1977).
