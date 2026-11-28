# Targeted maximum likelihood estimation

Let $O_1,\dots,O_n$ be i.i.d. from $P_0$ in a model $\mathcal M$, let $\psi = \Psi(P)$ be a pathwise differentiable parameter with efficient influence curve $D^*(P)(O)$, and let $\hat P^0$ be an initial (e.g. machine-learning) estimate of the relevant part of $P_0$.

**Targeted maximum likelihood (TMLE).** Choose a parametric *fluctuation* submodel $\{\hat P^0(\epsilon) : \epsilon\}$ through $\hat P^0$ at $\epsilon = 0$ whose score at $\epsilon = 0$ spans $D^*(\hat P^0)$, estimate $\epsilon$ by maximum likelihood, $\hat\epsilon = \arg\max_\epsilon \sum_i \log \hat p^0(\epsilon)(O_i)$, update $\hat P^1 = \hat P^0(\hat\epsilon)$, and iterate until $\hat\epsilon \approx 0$. The TMLE is the plug-in estimate $\hat\psi = \Psi(\hat P^*)$ at the final update $\hat P^*$, which solves the efficient-influence-curve estimating equation

$$\frac1n\sum_{i=1}^n D^*(\hat P^*)(O_i) = 0.$$

Solving this equation is an algebraic property of the fitted $\hat P^*$; efficiency needs conditions on the fitted estimators, not only the population identity $\mathbb E_{P_0} D^*(P_0)(O) = 0$. In the source's Theorem 1, $\mathcal M$ is convex, $\Psi$ is linear, so that $\Psi(P) - \Psi(P_0) = -\mathbb E_{P_0} D^*(P)(O)$, $\hat P^* \in \mathcal M$ with $p_0/\hat p^*$ bounded on the support of $p_0$, and the number of iterations $K(n)$ is large enough that the estimating equation holds up to a remainder $R(n, K(n)) = \frac1n\sum_i D^*(\hat P^*)(O_i) = o_P(n^{-1/2})$. Then $\hat\psi - \psi_0 = \frac1n\sum_i \{D^*(\hat P^*)(O_i) - \mathbb E_{P_0} D^*(\hat P^*)(O)\} + R(n, K(n))$. If moreover $D^*(\hat P^*)$ falls in a $P_0$-Donsker class with probability tending to $1$ and $\mathbb E_{P_0}\{D^*(\hat P^*) - D^*(P_1)\}^2(O) \to 0$ in probability for some $P_1 \in \mathcal M$, then $\hat\psi$ is asymptotically linear with influence curve $D^*(P_1) - \mathbb E_{P_0} D^*(P_1)(O)$; when $P_1 = P_0$ this gives $\hat\psi - \psi_0 = n^{-1}\sum_i D^*(P_0)(O_i) + o_P(n^{-1/2})$, so $\hat\psi$ is asymptotically efficient.

**Point-treatment example.** For $O = (W, A, Y)$ with binary $A$ and $Y \in [0,1]$, $\psi = \mathbb E_W\{\bar Q(1,W) - \bar Q(0,W)\}$ with $\bar Q(a,w) = \mathbb E(Y\mid A=a,W=w)$ and propensity $g(w) = P(A=1\mid W=w)$. Assume overlap, $\delta \le g(W) \le 1 - \delta$ a.s. for some $\delta > 0$, so that both inverse probabilities below are bounded and $D^*$ is square integrable; the fitted $\hat g$ is likewise truncated to $[\delta, 1 - \delta]$. The efficient influence curve is

$$D^*(O) = H_g(A,W)\{Y - \bar Q(A,W)\} + \bar Q(1,W) - \bar Q(0,W) - \psi, \qquad H_g(A,W) = \frac{A}{g(W)} - \frac{1-A}{1-g(W)}.$$

With initial $\hat{\bar Q}^0$ and $\hat g$, the logistic fluctuation $\operatorname{logit}\hat{\bar Q}^0(\epsilon) = \operatorname{logit}\hat{\bar Q}^0 + \epsilon H_{\hat g}$ (the "clever covariate") is fitted by logistic regression of $Y$ on $H_{\hat g}(A,W)$ with offset $\operatorname{logit}\hat{\bar Q}^0(A,W)$; one step suffices, and

$$\hat\psi = \frac1n\sum_{i=1}^n\big\{\hat{\bar Q}^1(1,W_i) - \hat{\bar Q}^1(0,W_i)\big\}.$$

## Depends on

- [Riesz representer and the doubly robust moment of a linear functional](riesz-representer-and-doubly-robust-moment.md)

## Expansion

At the MLE $\hat\epsilon$ the score of the fluctuation vanishes, and because that score is (or spans) $D^*$ at the updated fit, the empirical mean of $D^*(\hat P^*)$ is zero; the plug-in then inherits the expansion of a one-step (estimating-equation) estimator while remaining a substitution estimator that respects the parameter's bounds. In the example the score of the logistic fluctuation is $H_{\hat g}(A,W)\{Y - \hat{\bar Q}(\epsilon)(A,W)\}$, the first term of $D^*$; the remaining terms have empirical mean zero by the empirical marginal of $W$, and since $H_{\hat g}$ does not change with $\epsilon$ the iteration converges in one step.

## Sources

- Mark J. van der Laan and Daniel Rubin, "Targeted Maximum Likelihood Learning", The International Journal of Biostatistics (2006), <https://doi.org/10.2202/1557-4679.1043>, Section 2, Eq. (10) and Theorem 1.
