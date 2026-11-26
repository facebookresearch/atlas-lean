# Time-changed Beta coalescents and Gompertz coalescence times

**Setting.** In Schweinsberg's supercritical Cannings model each individual produces i.i.d. potential offspring with law $X$, $E(X) = \mu > 1$ and heavy tail

$$P(X \ge k) \sim C k^{-\alpha} \quad (k \in \mathbb{N},\ C > 0),$$

and the next generation is sampled from the pool of potential offspring. For fixed size $N$ and $1 \le \alpha < 2$, the rescaled genealogy of $n$ sampled individuals converges to the $\mathrm{Beta}(2-\alpha,\alpha)$-$n$-coalescent. With variable sizes $N_r$ (generations counted backward, $N = N_0$), let $\nu$ be a positive population size profile, $N^{-1}N_{\lfloor tc_N^{-1}\rfloor} \to \nu(t)$, with $c_1(t)N \le N_r \le c_2(t)N$.

**Lemma (enough offspring).** If $d_{N,r} = N_{r-1} - N_r > 0$ and $d_{N,r}/N \le d_N$ for a null sequence $(d_N)$ uniformly in $r \le c_N^{-1}t$, then $P\big(\sum_{i=1}^{N_r} X^{(r)}_i < N_{r-1}\big) \le A^N$ for some $A < 1$.

**Theorem.** For $\alpha \in [1,2)$ and every profile $\nu$ there are admissible sizes $(N_r)$ for which the ancestral partitions satisfy

$$\big(\tilde{\mathcal{R}}^{(N)}_{[c_N^{-1}t]}\big)_{t\ge0} \xrightarrow{d} \big(\Pi_{\mathcal{G}(t)}\big)_{t\ge0}, \qquad \mathcal{G}(t) = \int_0^t \nu(s)^{1-\alpha}\,ds,$$

in the Skorokhod sense, where $\Pi$ is the $\mathrm{Beta}(2-\alpha,\alpha)$-$n$-coalescent.

**Corollary (exponential growth).** If $\nu(t) = e^{-\rho t}$ with $\rho > 0$ (sizes $N_{r-1} = \lfloor N_r(1 - c_N\rho)\rfloor$) and $c_N = cN^{-\gamma} + o(N^{-\gamma})$ with $\gamma > 0$, then

$$\mathcal{G}(t) = \int_0^t e^{\rho\gamma s}\,ds = \frac{e^{\rho\gamma t} - 1}{\rho\gamma}.$$

Hence, given that the last coalescence happened at time $t_0$ and left $b$ lineages with total merger rate $\lambda_b$, the waiting time $T$ to the next merger is Gompertz distributed with parameters $\lambda_b e^{\rho\gamma t_0}$ and $\rho\gamma$:

$$P_{t_0}(T \le t) = 1 - \exp\!\Big(-\frac{\lambda_b}{\rho\gamma}\big(e^{\rho\gamma(t+t_0)} - e^{\rho\gamma t_0}\big)\Big).$$

This generalizes the Gompertz inter-coalescence times of Kingman's coalescent under exponential growth to every Λ-coalescent arising with $c_N$ regularly varying of index $-\gamma$.

## Depends on

- [Time-changed Λ-coalescent limits of modified Moran models](time-changed-lambda-coalescent-limits-of-modified-moran-models.md)

## Expansion

Because the potential offspring pool has size about $\mu N_r$, the lemma shows that growth by $o(N)$ individuals per generation is covered except on an event of exponentially small probability, so sampling from the pool defines a valid Cannings model with variable size. For this model $c_N \asymp N^{1-\alpha}$, hence $c_{N,r}/c_N \to \nu(t)^{1-\alpha}$, and the same sufficient condition used for modified Moran models yields the time-changed Beta limit. Under the time change $\mathcal{G}$, the integrated hazard of the next merger between $t_0$ and $t_0+t$ is $\lambda_b\,(\mathcal{G}(t_0+t) - \mathcal{G}(t_0))$, which for the exponential profile is the Gompertz cumulative hazard. (The printed formula in the source drops the minus sign in the exponent; the displayed form is the correct survival function.)

## Sources

- Fabian Freund, "Cannings models, population size changes and multiple-merger coalescents", arXiv:1902.02155 (2019), Section 2, Lemma 2.7, Theorem 2.8 and Corollary 2.9, <https://doi.org/10.48550/arXiv.1902.02155>.
