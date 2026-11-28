# Consistency of maximum likelihood in context-dependent pair HMMs

**Model.** An alignment of two homologous DNA sequences $X_{1:n}$ and $Y_{1:m}$ over a finite alphabet $\mathcal{A}$ is a hidden lattice path $Z_t = \sum_{s\le t}\varepsilon_s$. Its steps are $M = (1,1)$ (homologous site), $I_X = (1,0)$ and $I_Y = (0,1)$, and $(\varepsilon_t)$ is a stationary ergodic Markov chain with $3\times 3$ transition matrix $\pi$. Given the path, the letters form an order-one Markov chain whose dependence acts only between successive homologous positions:

$$\Pr(X_{N_s}, Y_{M_s}\mid\cdots) = \begin{cases}\tilde h(X_{N_s},Y_{M_s}\mid X_{N_{s-1}},Y_{M_{s-1}}) & \varepsilon_s = \varepsilon_{s-1} = M,\\ h(X_{N_s},Y_{M_s}) & \varepsilon_s = M \ne \varepsilon_{s-1},\\ f(X_{N_s}) & \varepsilon_s = I_X,\\ g(Y_{M_s}) & \varepsilon_s = I_Y.\end{cases}$$

The context-dependent substitution kernel $\tilde h$ is the new ingredient compared with a classical pair HMM. The parameter is $\theta = (\pi, f, g, h, \tilde h)$, with the identifiability requirements $h \ne f\otimes g$, $\tilde h(\cdot\mid c,d) \ne f\otimes g$ for some $c,d$, and $\tilde h \ne h$. The statistical-alignment criterion is

$$w_{n,m}(\theta) = \log\Pr_\theta\big(\exists s : Z_s = (n,m);\ X_{1:n}, Y_{1:m}\big),$$

summed over all paths from $(0,0)$ to $(n,m)$. Let $w_t(\theta) = \log Q_\theta(X_{1:N_t}, Y_{1:M_t})$ along the true alignment length $t$. Let $\Theta_0$ be the parameters with all coordinates positive, $\Theta_\delta$ those with all coordinates $\ge \delta$, and $\Theta_{\rm marg}\subset\Theta_0$ those whose $h$ and $\tilde h(\cdot\mid b,c)$ have marginals $f$ and $g$.

**Theorem.** Let the true parameter be $\theta_0 \in \Theta_0$. For every $\theta\in\Theta_0$:

1. $t^{-1}w_t(\theta)$ converges almost surely and in $L^1$ to $w(\theta) = \lim_t t^{-1}\mathbb{E}_{\theta_0}w_t(\theta) = \sup_t t^{-1}\mathbb{E}_{\theta_0}w_t(\theta)$;
2. $w(\theta_0) \ge w(\theta)$, with strict inequality if (A) $\mathbb{E}_\theta(\varepsilon_1)$ is not proportional to $\mathbb{E}_{\theta_0}(\varepsilon_1)$, or (B) $\theta_0, \theta\in\Theta_{\rm marg}$ and $f\ne f_0$ or $g\ne g_0$;
3. $\{t^{-1}w_t\}_{t\ge1}$ is uniformly equicontinuous on each $\Theta_\delta$.

**Corollary.** Suppose the parameters are given through evolutionary rates $\theta = \theta(\beta)$, and $\beta\mapsto w(\theta(\beta))$ has the unique maximizer $\beta_0$ on the parameter set $B_\delta$. Then the maximum-likelihood estimator $\hat\beta_{n,m}$ converges almost surely to $\beta_0$. If the prior $\nu$ charges every neighbourhood of $\beta_0$, the posterior distributions converge almost surely to the point mass at $\beta_0$.

## Expansion

Part 1 is a subadditive ergodic argument: $\mathbb{E}\,w_t$ is superadditive in $t$ because concatenating alignments of consecutive blocks gives a lower bound on the summed path probability. Part 2 is a Kullback–Leibler inequality. Identifiability fails only up to the rescaling of the path drift and up to the letter marginals, which conditions (A) and (B) exclude. With equicontinuity, Wald's classical argument turns pointwise convergence of the criterion into consistency of its maximizer. Since $n\vee m \le t \le n+m$, the conclusions also hold as $n, m\to\infty$ without knowing the true alignment length. In practice, the criterion and the posterior over alignments are computed with forward–backward recursions on the extended state space, and parameters are fitted by stochastic-approximation EM (SAEM).

## Depends on

- [Joint weight of sequences and an alignment's state path](../../sequence-alignment/pair-hidden-markov-models/align-prob.md)

## Proof depends on

- [Kingman's subadditive ergodic theorem (nonnegative case)](../../../../Dynamics/ergodic-theory/kingman-s-subadditive-ergodic-theorem/kingman-subadditive.md)

## Sources

- A. Arribas-Gil and C. Matias, "A context dependent pair hidden Markov model for statistical alignment", arXiv:1107.2798 (2011), Section 2 (model and identifiability conditions) and Section 3 (consistency theorem and corollary), <https://doi.org/10.48550/arXiv.1107.2798>.
