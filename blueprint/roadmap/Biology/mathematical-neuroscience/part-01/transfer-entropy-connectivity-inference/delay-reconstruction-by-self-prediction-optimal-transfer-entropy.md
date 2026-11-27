# Delay reconstruction by self-prediction-optimal transfer entropy

Let $(X_t)$ and $(Y_t)$ be jointly stationary discrete-time random processes admitting finite-dimensional state-space (delay-embedding) representations $\mathbf{X}_t^{d_x}$ and $\mathbf{Y}_t^{d_y}$, the state of each process being a sufficient statistic for its own future. Suppose $X$ drives $Y$ with a single interaction delay $\delta > 0$, so that $Y_t$ depends on $X$ only through $\mathbf{X}_{t-\delta}^{d_x}$ (beyond its own past state $\mathbf{Y}_{t-1}^{d_y}$). For a delay parameter $u$, the **self-prediction-optimal transfer entropy** is the conditional mutual information

$$\mathrm{TE}_{\mathrm{SPO}}(X \to Y, t, u) = I\big(Y_t \,;\, \mathbf{X}_{t-u}^{d_x} \,\big|\, \mathbf{Y}_{t-1}^{d_y}\big),$$

in which the target's past state is always taken immediately before the predicted sample (lag one), whatever the source lag $u$.

**Theorem.** $\mathrm{TE}_{\mathrm{SPO}}(X\to Y,t,u)$ is maximal at $u = \delta$; this remains true when there is additional coupling from $Y$ back to $X$. Hence the interaction delay is recovered as

$$\hat\delta = \arg\max_u \mathrm{TE}_{\mathrm{SPO}}(X \to Y, t, u).$$

Conditioning instead on the target state at the same lag as the source, $I(Y_t ; \mathbf{X}_{t-u} \mid \mathbf{Y}_{t-u})$, agrees with $\mathrm{TE}_{\mathrm{SPO}}$ only at $u=1$ and does not in general peak at the true delay, because it mixes information storage in $Y$ with transfer from $X$.

## Depends on

- [Conditional mutual information of a finite joint law](../../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)

## Expansion

If $u < \delta$, the source state $\mathbf{X}_{t-u}$ lies in the relative future of the influence that reaches $Y_t$, so (given the target's past) it carries less information about $Y_t$. If $u > \delta$, its influence on $Y$ has already arrived before time $t$ and is absorbed into $\mathbf{Y}_{t-1}$, so conditioning removes it. The proof reads off the causal graph of the coupled processes that, for $u \ne \delta$, the source state $\mathbf{X}_{t-u}$ is d-separated from $Y_t$ by the joint variable $(\mathbf{X}_{t-\delta}, \mathbf{Y}_{t-1})$, giving a Markov chain $\mathbf{X}_{t-u} \to (\mathbf{X}_{t-\delta}, \mathbf{Y}_{t-1}) \to Y_t$ (Eqs. (9)–(11)); the data-processing inequality (Eq. (12)) and the chain rule for mutual information then give $\mathrm{TE}_{\mathrm{SPO}}(u) \le \mathrm{TE}_{\mathrm{SPO}}(\delta)$. In practice the functional is scanned over $u$ with nearest-neighbour (Kraskov-type) estimators and the argmax is taken as the delay estimate.

## Sources

- M. Wibral, N. Pampu, V. Priesemann, F. Siebenhühner, H. Seiwert, M. Lindner, J. T. Lizier and R. Vicente, "Measuring information-transfer delays", PLoS ONE 8(2) (2013), e55809, Methods, Eqs. (6)–(12) and Theorem 1, <https://doi.org/10.1371/journal.pone.0055809>, PMCID: PMC3585400.
- T. Schreiber, "Measuring information transfer", Physical Review Letters 85 (2000), 461–464, <https://doi.org/10.1103/PhysRevLett.85.461>.
