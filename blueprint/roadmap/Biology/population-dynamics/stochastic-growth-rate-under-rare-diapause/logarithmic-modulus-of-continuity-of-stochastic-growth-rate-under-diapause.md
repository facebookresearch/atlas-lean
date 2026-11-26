# Logarithmic modulus of continuity of the stochastic growth rate under rare diapause

**Model.** An age-structured population with $d$ age classes $0, \dots, d-1$ is updated each year by the i.i.d. random Leslie matrix

$$L_t = \begin{pmatrix} 0 & 0 & \cdots & 0 & B_t \\ S_t^{(0)} & 0 & \cdots & 0 & 0 \\ 0 & S_t^{(1)} & \cdots & 0 & 0 \\ \vdots & & \ddots & & \vdots \\ 0 & 0 & \cdots & S_t^{(d-2)} & 0 \end{pmatrix},$$

where $S_t^{(j)} \in (0,1)$ is survival from age class $j$ to $j+1$ in year $t$ and $B_t > 0$ is the fecundity of an individual reaching the final class (births occur only at that fixed age, so generations have constant length $d$). **Diapause** of size $\epsilon$ adds diagonal entries $\epsilon \widehat A^{(j)}_t$: a small fraction of class $j$ stays in class $j$ for a year. Write $R_T(\epsilon)$ for the product of the first $T$ generation matrices and

$$a(\epsilon) = \lim_{T\to\infty} T^{-1} \log R_T(\epsilon)_{ij}$$

for the stochastic growth rate per generation (for $\epsilon > 0$ the limit exists almost surely, is deterministic, and does not depend on $i,j$). Set

$$\sigma_*^2 = \operatorname{Var}\Big(\log\frac{S_t^{(0)}}{B_t}\Big) + \operatorname{Var}\Big(\log\frac{B_t}{S_t^{(d-2)}}\Big) + \sum_{j=1}^{d-2}\operatorname{Var}\Big(\log\frac{S_t^{(j)}}{S_t^{(j-1)}}\Big).$$

**Theorem.** Suppose the vital rates $(S_t^{(0)}, \dots, S_t^{(d-2)}, B_t)$ are not all deterministic. Then

$$0 < \frac{\sigma_*^2}{2\pi d} \le \liminf_{\epsilon \downarrow 0}\, (\log \epsilon^{-1})\,\big(a(\epsilon) - a(0)\big).$$

If moreover $\log B_t$ and every $\log S_t^{(j)}$ have sub-Gaussian tails, then

$$0 < \liminf_{\epsilon\downarrow 0} (\log\epsilon^{-1})\big(a(\epsilon) - a(0)\big) \le \limsup_{\epsilon\downarrow 0} (\log\epsilon^{-1})\big(a(\epsilon) - a(0)\big) < \infty,$$

so $a$ has modulus of continuity exactly $1/\log\epsilon^{-1}$ at $0$, and in particular is not differentiable there.

**General form.** The statement is a case of a theorem for random matrix migration models: if two sites $i \ne j$ share the maximal mean log growth rate $\mu_i = \mu_j$, the site log growth rates $X^{(i)}_t, X^{(j)}_t$ do not coincide almost surely, the migration matrices are adapted to a connected migration graph, and migration rates are scaled by $\epsilon$, then $a(\epsilon) - a(0) \ge (1 + o(1))\,\sigma_*^2 / (2\pi \log \epsilon^{-1})$, with $\sigma_*^2$ a maximal cycle-averaged variance of log-rate differences. Grouping a diapause model into $d$-year steps gives a cyclic migration graph on the age classes in which every class has the same mean growth rate.

## Expansion

Since any linear cost of diapause is $O(\epsilon)$ and $1/\log\epsilon^{-1} \gg \epsilon$, a small random delay in development is always favored by selection over a fixed generation length. The lower bound comes from strategies that switch site only when the accumulated log-rate difference random walk has made an excursion of height of order $\log\epsilon^{-1}$: each switch costs a factor $\epsilon$, i.e. $\log\epsilon^{-1}$ in log growth, while an invariance principle (the expected maximum of Brownian motion on $[0,1]$ is $\sqrt{2/\pi}$) quantifies the gain; optimizing the block length yields $\sigma_*^2/(2\pi)$. The upper bound uses a packing bound on trajectories with $k$ switches and Orlicz-norm chaining under sub-Gaussian tails.

## Sources

- David Steinsaltz, Shripad Tuljapurkar, "Stability of fixed life histories to perturbation by rare diapause", arXiv (2018). Theorem 1, Corollary 2, equation for $\sigma_*^2$ in the diapause setting. <https://doi.org/10.48550/arXiv.1809.04027>
