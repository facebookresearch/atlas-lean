# Exponential relaxation and vanishing signal diffusion in volume-filling chemotaxis

For the multispecies volume-filling Keller–Segel system ($\partial_tu_i=\nabla\cdot(J_i-u_i\sum_kJ_k)$ with $J_i=\alpha_iu_i^{m_i-1}\nabla u_i+u_i\sum_k\chi_{ik}\nabla c_k$, $\partial_tc_j=D_j\Delta c_j-\lambda_jc_j+\sum_kb_{jk}u_k$, no-flux conditions, $\sum_{i=0}^nu_i=1$), let $u_i^\infty=|\Omega|^{-1}\int_\Omega u_i^0$ and $c_j^\infty=\lambda_j^{-1}\sum_kb_{jk}u_k^\infty$. Write $b'=(b_{ji}-b_{j0})$, $\chi'=(\chi_{ij}-\chi_{0j})$, $\alpha_*=\min_{i\ge1}\alpha_i$, $D_*=\min_jD_j$, $\lambda_*=\min_j\lambda_j$, $C_P$ the Poincaré constant and $\|\cdot\|_2$ the spectral norm.

**Theorem (long-time behavior).** Let $1\le m_i\le2$ and

$$\frac{C_P^2\|b'\|_2^2\|\chi'\|_2^2}{4\alpha_*^2D_*\lambda_*}<1 .$$

Then every weak solution satisfying the entropy inequality converges exponentially to the homogeneous state: for some $C,\mu>0$,

$$\sum_{i=1}^n\|u_i(t)-u_i^\infty\|_{L^2}^2+\sum_{j=1}^g\|c_j(t)-c_j^\infty\|_{L^2}^2\le Ce^{-\mu t}.$$

**Theorem (vanishing diffusion limit).** Let $\partial\Omega\in C^{1,1}$, $1\le m_i\le2$, and set $D_j=\varepsilon$ for all $j$. Along a subsequence, as $\varepsilon\to0$, $u_i^\varepsilon\to u_i$, $c_j^\varepsilon\to c_j$ and $\varepsilon\Delta c_j^\varepsilon\to0$ strongly in $L^2(\Omega\times(0,T))$, where $(u,c)$ solves the same cell equations coupled to the non-diffusing signal ODEs $\partial_tc_j=-\lambda_jc_j+\sum_kb_{jk}u_k$.

So when cell motility and signal diffusion dominate the differential chemotactic coupling, no pattern survives. Without signal diffusion the system is still well-posed in the weak sense.

## Depends on

- [Global weak solutions of the multispecies volume-filling Keller–Segel system](global-weak-solutions-of-the-multispecies-volume-filling-keller-segel-system.md)

## Expansion

Relaxation uses the relative entropy $h(\bar q|\bar q^\infty)=\sum_i(u_i\log\frac{u_i}{u_i^\infty}-u_i+u_i^\infty)+\frac K2\sum_j(c_j-c_j^\infty)^2$. Along solutions its derivative is bounded by $-C_P^{-2}(\alpha_*-\epsilon)\int\sum_i(u_i-u_i^\infty)^2-K\big(\lambda_*-\frac{C_P^2\|b'\|_2^2\|\chi'\|_2^2}{4\epsilon^2D_*}\big)\int\sum_j(c_j-c_j^\infty)^2$. The hypothesis is exactly what allows $\epsilon<\alpha_*$ making both coefficients negative, and Grönwall's lemma gives the exponential rate. Only differences $b_{ji}-b_{j0}$, $\chi_{ij}-\chi_{0j}$ enter because $u_0=1-\sum_{i\ge1}u_i$. For the limit $D_j\to0$ the entropy $h_3=\sum_iu_i(\log u_i-1)+\frac K2\sum_j|\nabla c_j|^2$ gives $\varepsilon$-uniform bounds on $\nabla u_i$ and $\varepsilon\|\Delta c_j\|^2$, and Aubin–Lions compactness passes to the limit.

## Sources

- N. Geltner, A. Jüngel, M. Zhang, *Analysis of a multispecies cross-diffusion Keller-Segel system with volume filling* (2026), Theorem 3 (long-time behavior, proof in Section 5) and Theorem 4 (vanishing diffusion limit, proof in Section 6). <https://doi.org/10.48550/arXiv.2607.12897>
