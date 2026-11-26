# Multiplicative Chernoff bounds for independent [0,1]-valued scores

Let $Y_1, \dots, Y_m$ be independent random variables with values in $[0,1]$ and $S = \sum_i Y_i$. For every real $t$, $\mathbb{E}[e^{tS}] \le \exp(\mathbb{E}[S](e^t - 1))$. Consequently:

1. if $\mathbb{E}[S] \le \mu$, then for every $\delta \ge 0$,

$$
\Pr[S \ge (1+\delta)\mu] \le \Big(\frac{e^{\delta}}{(1+\delta)^{1+\delta}}\Big)^{\mu} \le \exp\Big(-\frac{\delta^2 \mu}{2 + \delta}\Big),
$$

and the last bound can be replaced by $\exp(-\delta^2\mu/3)$ when $0 \le \delta \le 1$;

2. if $\mathbb{E}[S] \ge \mu$, then $\Pr[S \le (1-\delta)\mu] \le \exp(-\delta^2\mu/2)$ for every $\delta \ge 0$;

3. for $0 \le \delta \le 1$, $\Pr\big[|S - \mathbb{E}[S]| \ge \delta\, \mathbb{E}[S]\big] \le 2\exp(-\delta^2 \mathbb{E}[S]/3)$.

## Proof sketch

Convexity of $y \mapsto e^{ty}$ gives $e^{ty} \le 1 + y(e^t - 1)$ on $[0,1]$, so each factor of the moment generating function is at most $1 + \mathbb{E}[Y_i](e^t - 1) \le \exp(\mathbb{E}[Y_i](e^t-1))$ and independence multiplies them. Markov's inequality with $t = \ln(1+\delta)$ gives the sharp upper tail, and $\ln(1+\delta) \ge 2\delta/(2+\delta)$ simplifies it. For the lower tail take $t = -\delta$ and use $e^{-\delta} \le 1 - \delta + \delta^2/2$.

## Proof depends on

- [Fixed-direction Chernoff bound](../../large-deviations/cram-r-s-theorem/cramer-upper-bound.md)

## Sources

- M. Mitzenmacher and E. Upfal, "Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis", Cambridge University Press, 2nd ed., 2017.
- N. Alon and J. H. Spencer, "The Probabilistic Method", Wiley, 4th ed., 2016.
- H. Chernoff, "A Measure of Asymptotic Efficiency for Tests of a Hypothesis Based on the Sum of Observations", Annals of Mathematical Statistics 23, 1952.
