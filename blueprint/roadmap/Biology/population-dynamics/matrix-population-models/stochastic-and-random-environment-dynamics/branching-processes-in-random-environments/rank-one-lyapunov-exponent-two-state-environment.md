# Lyapunov exponent for rank-one mean matrices in a two-state Markov environment

**Environment.** Let $s_1, s_2 \in (0, 1]$ with $s_1 s_2 < 1$ and let $(I_n)_{n \ge 0}$ be the stationary Markov chain on $\{1, 2\}$ with transition matrix

$$P_I = \begin{pmatrix} 1 - s_1 & s_1 \\ s_2 & 1 - s_2 \end{pmatrix}, \qquad \pi_I = \Bigl(\frac{s_2}{s_1 + s_2}, \frac{s_1}{s_1 + s_2}\Bigr), \quad I_0 \sim \pi_I,$$

so $s_e$ is the probability of leaving environment $e$. A $p$-type branching process $(Z_n)$ in this environment has mean offspring matrix $M(I_n)$ in generation $n$, and its Lyapunov exponent is

$$\varphi_Z = \lim_{n \to \infty} \frac1n \log \lVert M(I_1) \cdots M(I_n) \rVert \quad \text{a.s.}$$

**Corollary.** If $\operatorname{rk} M(e) = 1$ and $\operatorname{tr} M(e) > 0$ for $e \in \{1, 2\}$ and $\operatorname{tr}(M(1)M(2)) > 0$, then almost surely

$$\varphi_Z = \frac{s_2}{s_1 + s_2}\log \operatorname{tr} M(1) + \frac{s_1}{s_1 + s_2}\log \operatorname{tr} M(2) + \frac{s_1 s_2}{s_1 + s_2}\log\frac{\operatorname{tr}(M(1)M(2))}{\operatorname{tr} M(1)\, \operatorname{tr} M(2)}.$$

For a 1-type process ($p = 1$) the last term vanishes and $\varphi_Z = E\log M(I_0)$; the correction term is the gain or loss from type-switching (e.g. between active and dormant individuals) that is coordinated with environmental changes.

## Proof depends on

- [Birkhoff pointwise ergodic theorem (ergodic case)](../../../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/birkhoff-pointwise-ergodic.md)

## Expansion

Write $M(e) = u_e v_e^\top$. A product of rank-one matrices telescopes: $M(i_1) \cdots M(i_n) = u_{i_1} \bigl(\prod_{m=1}^{n-1} v_{i_m}^\top u_{i_{m+1}}\bigr) v_{i_n}^\top$, so, with $r(i, j) = v_i^\top u_j$, $\frac1n \log\lVert M(I_1)\cdots M(I_n)\rVert = \frac1n\sum_{m=1}^{n-1}\log r(I_m, I_{m+1}) + O(1/n)$. The hypotheses make every $r(i,j)$ that occurs positive, and the stationary chain is irreducible because $s_1, s_2 > 0$, so the shift on its path space is ergodic; the [Birkhoff pointwise ergodic theorem](../../../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/birkhoff-pointwise-ergodic.md) applied to $\log r(I_0, I_1)$ gives $\varphi_Z = E \log r(I_0, I_1)$ almost surely (the authors' Lemma 3.1). Here $r(e, e) = \operatorname{tr} M(e)$ and $r(1,2) r(2,1) = \operatorname{tr}(M(1)M(2))$. Since $\pi_1 P_{12} = \pi_2 P_{21} = s_1 s_2/(s_1 + s_2)$,

$$E\log r(I_0, I_1) = \pi_1(1 - s_1)\log\operatorname{tr}M(1) + \pi_2(1 - s_2)\log\operatorname{tr}M(2) + \frac{s_1 s_2}{s_1 + s_2}\log\operatorname{tr}(M(1)M(2)),$$

which rearranges to the stated formula.

## Sources

- J. Blath, F. Hermann and M. Slowik, "A branching process model for dormancy and seed banks in randomly fluctuating environments", *Journal of Mathematical Biology* (2021), article 17, <https://doi.org/10.1007/s00285-021-01639-6> (PMC8289800). Definition 2.3, Lemma 3.1 and Corollary 3.2.
