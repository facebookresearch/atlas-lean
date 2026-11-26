# Noise sensitivity of a class from bounds on total influence

Let $0 < \delta \le 1/2$ and $m = \lfloor 1/\delta \rfloor$. Let $\mathcal{B} = (\mathcal{B}_n)$ be a class of Boolean functions closed under negating, identifying and adding dummy variables (for every $f \in \mathcal{B}_n$, string $z$ and map $\pi : [n] \to [m]$, the function $w \mapsto f(z \cdot (w \circ \pi))$ on $\{-1,1\}^m$ is in $\mathcal{B}_m$), and suppose members of $\mathcal{B}_m$ have total influence at most $A(m)$. Then every $f \in \mathcal{B}$ satisfies $\mathrm{NS}_\delta[f] \le A(m)/m$. Without closure under adding dummy variables the statement fails (e.g. $\{\chi_1, -\chi_1\}$ on one bit).

## Proof sketch

Realize $\delta$-noise by randomly assigning each coordinate to one of $m$ groups and flipping a random group: partition the coordinates randomly into $m$ blocks, so that $f$ restricted along a random $z$ becomes a member of $\mathcal{B}_m$ in which flipping one random block variable corresponds to the noise. Then $\mathrm{NS}_\delta[f]$ is at most the average influence of a random coordinate of that member, i.e. $\mathbf{I}/m \le A(m)/m$.

## Depends on

- [Noise sensitivity](noise-sensitivity.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
