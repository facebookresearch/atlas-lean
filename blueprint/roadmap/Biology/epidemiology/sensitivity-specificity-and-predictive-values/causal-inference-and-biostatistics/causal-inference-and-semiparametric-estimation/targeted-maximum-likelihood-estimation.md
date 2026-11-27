# Targeted maximum likelihood estimation

Let $O_1,\dots,O_n$ be i.i.d. from $P_0$ in a model $\mathcal M$, let $\psi = \Psi(P)$ be a pathwise differentiable parameter with efficient influence curve $D^*(P)(O)$, and let $\hat P^0$ be an initial (e.g. machine-learning) estimate of the relevant part of $P_0$.

**Targeted maximum likelihood (TMLE).** Choose a parametric *fluctuation* submodel $\{\hat P^0(\epsilon) : \epsilon\}$ through $\hat P^0$ at $\epsilon = 0$ whose score at $\epsilon = 0$ spans $D^*(\hat P^0)$, estimate $\epsilon$ by maximum likelihood, $\hat\epsilon = \arg\max_\epsilon \sum_i \log \hat p^0(\epsilon)(O_i)$, update $\hat P^1 = \hat P^0(\hat\epsilon)$, and iterate until $\hat\epsilon \approx 0$. The TMLE is the plug-in estimate $\hat\psi = \Psi(\hat P^*)$ at the final update $\hat P^*$, which solves the efficient-influence-curve estimating equation

$$\frac1n\sum_{i=1}^n D^*(\hat P^*)(O_i) = 0.$$

Solving this equation is an algebraic property of the fitted $\hat P^*$. Under the usual conditions for asymptotically linear estimators, which concern the fitted estimators and not only the population identity $\mathbb E_{P_0} D^*(P_0)(O) = 0$ (second-order remainder $o_P(n^{-1/2})$ and a Donsker or sample-splitting condition), $\hat\psi - \psi_0 = n^{-1}\sum_i D^*(P_0)(O_i) + o_P(n^{-1/2})$, so $\hat\psi$ is efficient, and it is doubly robust when the remainder has a product structure.

**Point-treatment example.** For $O = (W, A, Y)$ with binary $A$ and $Y \in [0,1]$, $\psi = \mathbb E_W\{\bar Q(1,W) - \bar Q(0,W)\}$ with $\bar Q(a,w) = \mathbb E(Y\mid A=a,W=w)$ and propensity $g(w) = P(A=1\mid W=w)$. Assume overlap, $\delta \le g(W) \le 1 - \delta$ a.s. for some $\delta > 0$, so that both inverse probabilities below are bounded and $D^*$ is square integrable; the fitted $\hat g$ is likewise truncated to $[\delta, 1 - \delta]$. The efficient influence curve is

$$D^*(O) = H_g(A,W)\{Y - \bar Q(A,W)\} + \bar Q(1,W) - \bar Q(0,W) - \psi, \qquad H_g(A,W) = \frac{A}{g(W)} - \frac{1-A}{1-g(W)}.$$

With initial $\hat{\bar Q}^0$ and $\hat g$, the logistic fluctuation $\operatorname{logit}\hat{\bar Q}^0(\epsilon) = \operatorname{logit}\hat{\bar Q}^0 + \epsilon H_{\hat g}$ (the "clever covariate") is fitted by logistic regression of $Y$ on $H_{\hat g}(A,W)$ with offset $\operatorname{logit}\hat{\bar Q}^0(A,W)$; one step suffices, and

$$\hat\psi = \frac1n\sum_{i=1}^n\big\{\hat{\bar Q}^1(1,W_i) - \hat{\bar Q}^1(0,W_i)\big\}.$$

## Depends on

- [Riesz representer and the doubly robust moment of a linear functional](riesz-representer-and-doubly-robust-moment.md)

## Expansion

At the MLE $\hat\epsilon$ the score of the fluctuation vanishes, and because that score is (or spans) $D^*$ at the updated fit, the empirical mean of $D^*(\hat P^*)$ is zero; the plug-in then inherits the expansion of a one-step (estimating-equation) estimator while remaining a substitution estimator that respects the parameter's bounds. In the example the score of the logistic fluctuation is $H_{\hat g}(A,W)\{Y - \hat{\bar Q}(\epsilon)(A,W)\}$, the first term of $D^*$; the remaining terms have empirical mean zero by the empirical marginal of $W$, and since $H_{\hat g}$ does not change with $\epsilon$ the iteration converges in one step.

## Sources

- Mark J. van der Laan and Daniel Rubin, "Targeted Maximum Likelihood Learning", The International Journal of Biostatistics (2006), <https://doi.org/10.2202/1557-4679.1043>.
