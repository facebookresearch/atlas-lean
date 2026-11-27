# Survival thresholds of an ageing branching random walk

**Model.** On a countable set $X$ each individual lives an Exp(1) lifetime; an individual born at $x$ at time $\bar t$ places children at $y$ at the arrival times of a Poisson process of intensity $\lambda r_{xy}(t - \bar t)$, with $r_{xy} \in L^1_{\mathrm{loc}}([0,\infty))$ non-negative (reproduction varies with age, e.g. rising to a peak and then declining). The mean offspring matrix is $m_{xy} = \lambda k_{xy}$ with

$$k_{xy} = \int_0^\infty r_{xy}(s)\,e^{-s}\,ds, \qquad \sup_x\sum_y m_{xy} < \infty .$$

Let $k^{(n)}_{xy}$ be the entries of $K^n$. *Local survival* at $x$ means $x$ is visited at arbitrarily large times with positive probability; *global survival* means the population never dies out with positive probability. $\lambda_s(x)$ and $\lambda_w(x)$ are the corresponding critical parameters.

**Theorem (local survival).** The process survives locally at $x$ iff

$$\lambda\,\limsup_{n\to\infty}\bigl(k^{(n)}_{xx}\bigr)^{1/n} > 1, \qquad\text{so}\qquad \lambda_s(x) = \frac{1}{\limsup_n (k^{(n)}_{xx})^{1/n}} = \sup\{\lambda : \Phi(x,x\mid\lambda) < 1\},$$

$\Phi(x,x\mid\lambda)$ being the first-return generating function of the mean matrix.

**Theorem (global survival).** $\lambda_w(x) \ge 1/\liminf_n\bigl(\sum_y k^{(n)}_{xy}\bigr)^{1/n}$, so the process dies out a.s. below this value; if the discrete-time counterpart (the generation-by-generation BRW with mean matrix $\lambda K$) is an $\mathcal{F}$-BRW, meaning that there are a finite set $Y$ and a surjection $g:X\to Y$ such that the expected offspring placed in each class, $\sum_{z\in g^{-1}(j)}k_{xz}$, depends only on $(g(x),j)$ (transitive and quasi-transitive BRWs are examples), global survival from $x$ holds iff $\lambda > 1/\liminf_n\bigl(\sum_y k^{(n)}_{xy}\bigr)^{1/n}$.

**Local modifications.** In this part the ageing BRWs are *irreducible*: for all $x,y\in X$ there is $n$ with $k^{(n)}_{xy}>0$, so $\lambda_s$ and $\lambda_w$ do not depend on $x$. An ageing BRW $(X,\mathcal{R})$ with rates $\mathcal R=(r_{xy})$ is a *local modification* of $(X,\mathcal{R}^*)$ if the set $\{x\in X:\ r_{xy}\ne r^*_{xy}\text{ for some }y\}$ is finite. If $\lambda_w<\lambda_s$ and $(X,\mathcal{R})$ is a local modification of $(X,\mathcal{R}^*)$, then (1) $\lambda_w^*\le\lambda_w$; (2) if $\lambda_w^*<\lambda_s^*$, then $\lambda_w^*=\lambda_w$; (3) if $\lambda_s^*\le\lambda_w$, then $\lambda_w^*=\lambda_s^*\le\lambda_w$, and if $\lambda_s^*>\lambda_w$, then $\lambda_w^*=\lambda_w<\lambda_s^*$. So an irreducible ageing BRW with a pure global survival phase ($\lambda_w<\lambda_s$) cannot be a local modification of an irreducible quasi-transitive one without such a phase.

## Expansion

Ageing changes the timing of births but, because lifetimes are Exp(1), each individual's expected lifetime offspring at $y$ is exactly $\lambda k_{xy}$, where $e^{-s}$ is the probability of being alive at age $s$. Survival questions depend only on the embedded generation-by-generation process, a discrete-time BRW with this mean matrix, so the classical spectral-radius criteria transfer with $K$ in place of the constant-rate matrix. Lowering late-life fertility therefore raises the survival thresholds by reducing $k_{xy}$, even when peak fertility is unchanged.

## Sources

- D. Bertacchi, E. Montanaro, F. Zucca, "Branching random walks with ageing", *Mathematics* 14(6) (2026), 1088, definition and first-moment matrix of Section 2, Theorems 3.1-3.3, Definition 4.1, Theorems 4.2 and 4.7, Corollary 4.8, <https://doi.org/10.3390/math14061088> (preprint arXiv:2602.22783).
