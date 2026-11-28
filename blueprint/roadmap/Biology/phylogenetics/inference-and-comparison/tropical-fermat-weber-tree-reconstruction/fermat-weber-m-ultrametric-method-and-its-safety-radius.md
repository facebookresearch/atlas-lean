# Fermat–Weber M-ultrametric method and its safety radius

**Setting.** Use the space $\mathcal U_M$ of $M$-ultrametrics, the tropical metric $d_{\mathrm{tr}}$, the tropical projection $\pi_M$ and the gap $w_{\min}$ from [the projection safety radius](safety-radius-of-the-tropical-projection-onto-m-ultrametrics.md); $\|x\|_{\mathrm{tr}} = \max_i x_i - \min_i x_i$. For a sample $S = \{v_1, \dots, v_n\} \subset \mathbb{R}^q/\mathbb{R}\mathbf 1$ the tropical **Fermat–Weber function** is $f_S(x) = \frac1n\sum_{i=1}^n d_{\mathrm{tr}}(x, v_i)$, and $\mathrm{FW}(S)$ is its set of minimizers. The **Fermat–Weber $M$-ultrametric method** returns $\pi_M(\mathrm{FW}(S))$. It has safety radius $s$ if, whenever $\mathrm{FW}(S)$ meets the relative interior of a maximal cone $K$ of the nested set fan and the perturbations satisfy $\sum_j \|\epsilon_j\|_{\mathrm{tr}} < s\,\tilde w_{\min}$, the set $\pi_M(\mathrm{FW}(S + \epsilon))$ still meets the relative interior of $K$; here $\tilde w_{\min} = \max\{w_{\min} : w \in \pi_M(\mathrm{FW}(S)) \cap K\}$.

**Statement.**

1. If $S \subset \mathcal U_M$, then $\mathrm{FW}(S) \cap \mathcal U_M = \pi_M(\mathrm{FW}(S))$, and this set is nonempty: a sample of $M$-ultrametrics (for example, equidistant trees) always has a tropical Fermat–Weber point that is itself an $M$-ultrametric.
2. For every matroid $M$, the Fermat–Weber $M$-ultrametric method has safety radius exactly $1/2$.
3. (Stochastic version.) For i.i.d. noise $\epsilon_j \sim N(0, \sigma^2 I_q)$, call $s$ an $\eta$-stochastic safety radius if $\sigma < s\,\sqrt 2\,\tilde w_{\min}/(n\sqrt{\log q})$ guarantees that $\pi_M(\mathrm{FW}(S + \epsilon))$ meets the relative interior of $K$ with probability at least $1 - \eta$. For every $\eta > 0$, $n, q$ and $M$ a nonzero $\eta$-stochastic safety radius exists, and it can be taken arbitrarily close to $1/8$ for $n, q$ large.

## Depends on

- [Safety radius of the tropical projection onto M-ultrametrics](safety-radius-of-the-tropical-projection-onto-m-ultrametrics.md)

## Expansion

The Fermat–Weber function satisfies the reverse Lipschitz bound $\frac1n d_{\mathrm{tr}}(x, \mathrm{FW}(S)) \le f_S(x) - \min f_S$, obtained from lower bounds on its directional derivatives, and perturbing the sample by $\epsilon$ moves $\mathrm{FW}(S)$ by tropical Hausdorff distance at most $2\sum_j \|\epsilon_j\|_{\mathrm{tr}}$. Since $w$ lies at tropical distance $w_{\min}$ from the boundary of $K$ and $\pi_M$ is non-expansive, a total perturbation below $\tilde w_{\min}/2$ moves some projected Fermat–Weber point by less than $\tilde w_{\min}$ and so keeps it in $K$. For Gaussian noise, $\|\epsilon_j\|_{\mathrm{tr}}$ is the range of $q$ normals, of order $2\sigma\sqrt{2\log q}$, which yields the stochastic radius.

## Sources

- S. Cox, J. Sabol, R. Talbut and R. Yoshida, "Tropical Fermat–Weber points over spaces of $M$-ultrametrics", *Vietnam Journal of Mathematics* (2026), Theorems 12, 17 and 19; Definitions 10, 11, 13 and 18; Lemmas 14 and 16, <https://doi.org/10.1007/s10013-026-00799-6> (preprint arXiv:2505.09584).
