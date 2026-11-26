# Low noise sensitivity gives low-degree spectral concentration

For every Boolean $f : \{-1,1\}^n \to \{-1,1\}$ and every $0 < \delta \le 1/2$,

$$
\mathbf{W}^{\ge 1/\delta}[f] = \sum_{|S| \ge 1/\delta} \hat f(S)^2 \le \frac{2}{1 - e^{-2}}\,\mathrm{NS}_\delta[f] \le 3\,\mathrm{NS}_\delta[f].
$$

In particular the Fourier spectrum of $f$ is $3\,\mathrm{NS}_\delta[f]$-concentrated on degree up to $1/\delta$.

## Proof sketch

This is the argument that bounds high-degree weight by total influence, with the weights $|S|$ replaced by $1 - (1 - 2\delta)^{|S|}$. By the Fourier formula for noise sensitivity, $2\,\mathrm{NS}_\delta[f] = \sum_S \big(1 - (1 - 2\delta)^{|S|}\big)\hat f(S)^2$. The weight $1 - (1 - 2\delta)^{k}$ is nonnegative and nondecreasing in $k$, and for $k \ge 1/\delta$ it is at least $1 - (1 - 2\delta)^{1/\delta} \ge 1 - e^{-2} \ge 2/3$.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Noise sensitivity](noise-sensitivity.md)

## Proof depends on

- [Low total influence implies low-degree spectral concentration](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/sum-sq-card-gt-le-of-pos.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014 (arXiv:2105.10386), Proposition 3.3.
