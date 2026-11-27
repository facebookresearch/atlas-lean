# Noise sensitivity of a class from bounds on total influence

Let $0 < \delta \le 1/2$ and $m = \lfloor 1/\delta \rfloor$. Let $\mathcal{B} = (\mathcal{B}_n)$ be a class of Boolean functions closed under negating, identifying and adding dummy variables (for every $f \in \mathcal{B}_n$, string $z$ and map $\pi : [n] \to [m]$, the function $w \mapsto f(z \cdot (w \circ \pi))$ on $\{-1,1\}^m$ is in $\mathcal{B}_m$), and suppose members of $\mathcal{B}_m$ have total influence at most $A(m)$. Then every $f \in \mathcal{B}$ satisfies $\mathrm{NS}_\delta[f] \le A(m)/m$. Without closure under adding dummy variables the statement fails (e.g. $\{\chi_1, -\chi_1\}$ on one bit).

## Proof sketch

Since $m \ge 2$ and $\delta \le 1/m \le 1/2$, and $\mathrm{NS}_\delta[f] = \frac12\sum_S\big(1 - (1 - 2\delta)^{|S|}\big)\hat f(S)^2$ is nondecreasing in $\delta$ on $[0, 1/2]$, it suffices to bound $\mathrm{NS}_{1/m}[f]$. Assign each coordinate independently to one of $m$ groups by a uniform $\pi : [n] \to [m]$, take a uniform $z$, and flip one uniform group $j$: each coordinate is flipped independently with probability $1/m$, so this realizes $1/m$-noise (not $\delta$-noise). The function $g_{z,\pi}(w) = f(z \cdot (w \circ \pi))$ lies in $\mathcal{B}_m$, and $\mathrm{NS}_{1/m}[f]$ equals the expected average influence $\mathbf{I}[g_{z,\pi}]/m \le A(m)/m$ (O'Donnell, Thm. 5.35).

## Depends on

- [Noise sensitivity](noise-sensitivity.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
