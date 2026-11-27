# KKL edge-isoperimetric theorem

For every nonconstant $f : \{-1,1\}^n \to \{-1,1\}$, writing $\tilde{\mathbf{I}} = \mathbf{I}[f]/\mathrm{Var}[f]$, some coordinate $i$ satisfies

$$\mathbf{Inf}_i[f] \ge \frac{9}{\tilde{\mathbf{I}}^2}\Big(\frac19\Big)^{\tilde{\mathbf{I}}}.$$

In particular, if $\mathbf{I}[f] \le K\,\mathrm{Var}[f]$ then some coordinate has influence at least $9^{-O(K)}$, and the maximum influence of a balanced function with total influence $O(1)$ is bounded below by a constant.

## Proof sketch

Write $u = \tilde{\mathbf{I}}$. Applying the small-set expansion form of hypercontractivity to the derivatives gives $\mathbf{Inf}_i^{(1/3)}[f] \le \mathbf{Inf}_i[f]^{3/2}$, so $\mathbf{I}^{(1/3)}[f] \le \sum_i \mathbf{Inf}_i[f]^{3/2} \le \sqrt{\max_i \mathbf{Inf}_i[f]}\,\mathbf{I}[f]$. On the other side $\mathbf{I}^{(1/3)}[f] = \sum_{S \ne \emptyset}|S|\,3^{1-|S|}\hat f(S)^2 \ge 3\sum_{S \ne \emptyset}3^{-|S|}\hat f(S)^2$. The weights $\hat f(S)^2/\mathrm{Var}[f]$ on nonempty $S$ form a probability distribution under which $\mathbb{E}|S| = u$, so Jensen's inequality for the convex $s \mapsto 3^{-s}$ gives $\sum_{S \ne \emptyset}3^{-|S|}\hat f(S)^2 \ge \mathrm{Var}[f]\,3^{-u}$. Hence $3\,\mathrm{Var}[f]\,3^{-u} \le \sqrt{\max_i\mathbf{Inf}_i[f]}\,\mathbf{I}[f]$; squaring and dividing by $\mathbf{I}[f]^2 = u^2\mathrm{Var}[f]^2$ gives the bound (O'Donnell, §9.6 and Ex. 9.29).

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [Stable influences are bounded by powers of influences](../noise-sensitivity-and-stable-influence/stable-influences-bounded-by-powers-of-influences.md)
- [Stable influence and total stable influence](../noise-sensitivity-and-stable-influence/stable-influence.md)
- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- J. Kahn, G. Kalai and N. Linial, "The Influence of Variables on Boolean Functions", FOCS 1988.
