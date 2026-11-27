# One AdaBoost round multiplies the exponential loss by $2\sqrt{\varepsilon_T(1-\varepsilon_T)}$

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. If $0 < \varepsilon_T < 1$, then

$$L(F_{T+1}) = L(F_T) \cdot 2 \sqrt{\varepsilon_T (1 - \varepsilon_T)},$$

where $L$ is the [exponential loss](exp-loss.md).

## Sources

- Y. Freund and R. E. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", *J. Comput. System Sci.* 55 (1997), 119–139, proof of Theorem 6; R. E. Schapire, "Explaining AdaBoost", in B. Schölkopf, Z. Luo and V. Vovk (eds.), *Empirical Inference: Festschrift in Honor of Vladimir N. Vapnik*, Springer (2013), Section 4.
