# Fano minimax lower bound for estimation over a separated packing

Let $\Theta$ be a parameter set, $\ell$ a nonnegative loss, $V$ a finite set with $|V| \ge 2$, and $\theta : V \to \Theta$ a $2\Delta$-separated packing ($\Delta \ge 0$): $\ell(t, \theta_v) + \ell(t, \theta_w) \ge 2\Delta$ for all $t$ and $v \ne w$. Let $P_v$ be the law of the observation under $\theta_v$, and suppose $\frac{1}{|V|}\sum_v D(P_v \| Q) \le \beta$ for some $Q$ dominating every $P_v$ (divergence in nats). Then every estimator $\hat t$, deterministic or randomized, satisfies

$$
\max_{v \in V} \mathbb{E}_{P_v}\,\ell(\hat t, \theta_v) \ge \Delta\Bigl(1 - \frac{\beta + \log 2}{\log |V|}\Bigr),
$$

and some $v$ has $P_v[\ell(\hat t, \theta_v) \ge \Delta] \ge 1 - (\beta+\log 2)/\log|V|$. For $n$ i.i.d. observations, $\beta$ may be taken as $n$ times the per-observation pairwise average divergence.

## Proof sketch

Separation turns an estimator into a test: let $\psi$ pick the $v$ minimizing $\ell(\hat t, \theta_v)$; whenever $\psi \ne v$, the loss at $\theta_v$ is at least $\Delta$. Hence the risk is at least $\Delta$ times the testing error, which Fano's bound controls. Divergences tensorize over i.i.d. samples.

## Depends on

- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

- [Fano's method: lower bound on the error of multiple hypothesis testing](fano-multiple-testing-lower-bound.md)

## Sources

- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
