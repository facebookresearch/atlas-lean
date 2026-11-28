# PAC bound for linearly combined model ensembles

With $K$ base models combined through $d$-dimensional simplex features, an optimistic version-space algorithm returns, with probability at least $1-\delta$, a policy within $\varepsilon + (3\sqrt{dK}+2)H\theta$ of optimal after $\tilde O\big(\frac{d^3K^2H^2}{\varepsilon^2}\log\frac{dKH}{\delta}\big)$ trajectories, independent of $|\mathcal{S}|$ and $|\mathcal{A}|$; it assumes an optimistic planning oracle.

**Setting.** The model class is the [linear combination of base models](linear-combination-of-base-models.md) $\{M(W) : W \in \mathcal{W}_0\}$ with approximation error $\theta$ for the true environment $M^\ast$, total rewards in $[0,1]$, horizon $H$ and initial distribution $P_1$; $v^\ast$ is the optimal value and $v^\pi = \mathbb{E}_{s\sim P_1}V^\pi_{M^\ast,1}(s)$.

**Algorithm.** Keep a version space $\mathcal{W}_t \subseteq \mathcal{W}_0$. In iteration $t$:

1. Pick the optimistic parameter $W_t = \arg\max_{W \in \mathcal{W}_{t-1}} v_W$ (an oracle call) and its optimal policy $\pi_t = \pi_{W_t}$.
2. Estimate $v^{\pi_t}$ by $\hat v_t$ from $n_{\mathrm{eval}}$ trajectories. Stop and output $\pi_t$ if $v_{W_t} - \hat v_t \le 3\varepsilon/4 + (3\sqrt{dK}+1)H\theta$.
3. Otherwise collect $n$ trajectories with $\pi_t$, form $\hat Z_t = \frac1n\sum_i\sum_h \bar V_{t,h}(s^{(i)}_h,a^{(i)}_h)\,\phi(s^{(i)}_h,a^{(i)}_h)^{\mathsf T}$ with $[\bar V_{t,h}(s,a)]_k = \mathbb{E}_{M_k}[r + V_{W_t,h+1}(s') \mid s,a]$, and the observed returns $\hat y_t = \frac1n\sum_i\sum_h \big(r^{(i)}_h + V_{W_t,h+1}(s^{(i)}_{h+1})\big)$. Algorithm 1 of the source prints $r^{(i)}_{h+1}$ here, an indexing slip: its trajectories end in $r^{(i)}_H$, and its estimate of the same target at $(s_h,a_h)$ uses $r_h + f_{t,h+1}(s_{h+1})$ (Eqs. (9)–(10) of arXiv:1910.10597v1). Keep the parameters with $|\hat y_t - \langle W, \hat Z_t\rangle| \le \varepsilon/(12\sqrt{dK}) + H\theta$.

**Theorem.** For $\varepsilon \in (0,1]$ and $\delta \in (0,1)$, run the algorithm with $n_{\mathrm{eval}} = \frac{32H^2}{\varepsilon^2}\log\frac{4T}{\delta}$ and $n = \frac{1800\,d^2KH^2}{\varepsilon^2}\log\frac{8dKT}{\delta}$, where $T = dK\log\frac{2\sqrt{2K}H}{\varepsilon}\big/\log\frac53$ bounds the number of iterations. Then with probability at least $1-\delta$ it terminates after at most

$$
\tilde O\Big(\frac{d^3K^2H^2}{\varepsilon^2}\log\frac{dKH}{\delta}\Big)
$$

trajectories and returns a policy whose value is at least $v^\ast - \varepsilon - (3\sqrt{dK}+2)H\theta$.

**Sample versus computation.** The bound counts real-environment trajectories only. The algorithm assumes an optimistic planning oracle over version spaces (Assumption 4.4) and the ability to compute $\pi_W$ and its values for any $W$. The source knows no efficient implementation of the optimistic step even for finite state-action spaces: it is a bilinear, non-convex problem.

## Depends on

- [Linear combination of base models](linear-combination-of-base-models.md)

## Proof depends on

- [Matrix Bernstein inequality, Hermitian case](../../../../../Probability/concentration-inequalities/matrix-concentration-inequalities/matrix-bernstein.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

Explore or terminate: if the test in step 2 fails, a value decomposition shows that the true model and $W_t$ disagree substantially on the projected data. Because predictions are linear in $W$ through $\langle W, \hat Z_t\rangle$, the new constraint cuts deeply through the version space. A volume argument bounds the number of iterations by $O(dK\log(\sqrt K H/\varepsilon))$ (the source's Lemma A.7). It uses the volume reduction for minimum-volume enclosing ellipsoids (Lemma A.6, adapted from Jiang et al. 2017). The per-iteration sample sizes come from Hoeffding's inequality for the Monte Carlo value estimate $\hat v_t$ and for the return estimate $\hat y_t$ (Lemmas A.8 and A.9), and from Bernstein's inequality for each entry of $\hat Z_t$ with a union bound over its $dK$ entries (Lemma A.9). The additive $(3\sqrt{dK}+2)H\theta$ term includes a value loss of at most $2H\theta$ for the policy of the best model in the class (Corollary A.4).

A complete expansion adds pages for the episodic simulation lemma between two models (the source's Lemma A.2), the value decomposition behind explore-or-terminate (Lemmas A.1 and A.5), the volume reduction for minimum-volume enclosing ellipsoids (Lemma A.6, from Jiang et al. 2017), and the iteration bound it yields (Lemma A.7). The dimension-one case of the matrix Bernstein inequality, applied to centered summands divided by the sample size and to their negatives, gives the two-sided bound for each entry of $\hat Z_t$.

## Sources

- A. Modi, N. Jiang, A. Tewari and S. Singh, "Sample Complexity of Reinforcement Learning using Linearly Combined Model Ensembles", International Conference on Artificial Intelligence and Statistics (AISTATS 2020), PMLR 108:2010–2020. Numbers from arXiv:1910.10597v1: Algorithm 1, Theorem 4.1, Corollaries 4.2–4.3, Assumption 4.4 and the computational discussion, Appendix A (Lemmas A.1, A.5–A.9, Corollary A.4). <https://arxiv.org/abs/1910.10597v1>
