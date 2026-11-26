# Volterra system for the Laplace transform of a multivariate Hawkes epidemic

**Setting.** A $d$-dimensional Hawkes process $N=(N_1,\dots,N_d)$ driven by $(\lambda^0,\phi)$ is a simple marked point process whose type-$i$ events have conditional intensity
$$\widetilde\lambda_i(t)=\lambda^0_i(t)+\sum_{j=1}^d\int_{[0,t)}\phi^j_i(t-u)\,N_j(\mathrm du),$$
with a nonnegative, locally integrable baseline $\lambda^0:\mathbb R_+\to\mathbb R_+^d$ and excitation kernels $\phi^j_i\ge0$. In a spatial epidemic, $N_i(t)$ counts infections in region $i$ up to time $t$, $\lambda^0$ is the rate of introductions, and $\phi^j_i$ is the infectivity profile of a case in region $j$ toward region $i$. Equivalently (cluster representation), introductions form independent Poisson processes with intensities $\lambda^0_i$, and every type-$j$ case independently generates its own type-$i$ offspring as a Poisson process with intensity $\phi^j_i$ measured from its own time. For $j'\in\{1,\dots,d\}$ let $\widetilde N^{j'}$ be the Hawkes process driven by $(\phi^{j'}_\bullet,\phi)$, the descendants (excluding itself) of a single type-$j'$ case at time $0$, and let $\widetilde N^0=N$.

**Zero and one events.** With $\Phi^{j'}_j(t)=\int_0^t\phi^{j'}_j(s)\,\mathrm ds$ and $\Phi^0_j=\int_0^t\lambda^0_j$,
$$\mathbb P(\widetilde N^{j'}(t)=0)=\exp\Bigl(-\sum_{j=1}^d\Phi^{j'}_j(t)\Bigr),\qquad \mathbb P(\widetilde N^{j'}(t)=e_i)=\Phi^{j'}_i(t)\exp\Bigl(-\sum_{j=1}^d\Phi^{j'}_j(t)\Bigr).$$

**Statement (single time).** For $a\in\mathbb R_+^d$ let $L^{j'}(a,t)=\mathbb E\exp\bigl(-\sum_ia_i\widetilde N^{j'}_i(t)\bigr)$. Then for $j'=0,1,\dots,d$ (with $\phi^0_j:=\lambda^0_j$),
$$L^{j'}(a,t)=\mathbb P(\widetilde N^{j'}(t)=0)\,\exp\Bigl(\sum_{j=1}^d\int_0^te^{-a_j}L^j(a,t-u)\,\phi^{j'}_j(u)\,\mathrm du\Bigr).$$
Thus the $d$ basic transforms $L^1,\dots,L^d$ solve a closed nonlinear Volterra system, and the transform for any baseline $\lambda^0$ is an explicit functional of them. The source proves the analogous system for joint transforms at several ordered times $t_1\le\cdots\le t_n$, obtained by splitting the introductions by the interval $[t_{k-1},t_k)$ in which they occur.

**Infinite divisibility.** Splitting $\lambda^0$ into $L$ equal parts shows that $N(t)$ is infinitely divisible; since $\mathbb P(N(t)=0)>0$, its Laplace transform has the form $p_0\exp\bigl(\sum_{l\ne0}\alpha_le^{-\langle a,l\rangle}\bigr)$ with a finite measure $\sum_l\alpha_l\delta_l$ of total mass $-\log p_0$, and the $\alpha_l$ are computed recursively from the count probabilities.

## Expansion

Condition on the introductions: they form a Poisson process, and the case introduced at time $u$ with type $j$ contributes $e_j$ plus an independent copy of $\widetilde N^j(t-u)$. The Poisson exponential formula gives $\log L^0(a,t)=\sum_j\int_0^t\bigl(e^{-a_j}L^j(a,t-u)-1\bigr)\lambda^0_j(u)\,\mathrm du$, which is the displayed equation after separating the $-1$ terms into the zero-event probability; the same argument applied to the first generation of a single case gives the equations for $j'\ge1$. Differentiating in $a$ at $a=0$ produces the moment equations.

## Sources

- B. Vieille, R. Senoussi and S. Soubeyrand, *Functional Laplace Transform of a Multivariate Hawkes Process, Subsequent Characteristics, and Numerical Approximations*, arXiv:2507.15370 (2025): Section 2 (population representation, Lemma 2.1, Theorem 2.2), Section 3 (Theorem 3.4 on infinite divisibility). <https://doi.org/10.48550/arXiv.2507.15370>
