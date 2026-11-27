# Sharp edge-isoperimetric inequality for the Boolean cube

For every $f : \{-1,1\}^n \to \{-1,1\}$, with $\alpha = \min(\Pr[f = 1], \Pr[f = -1])$,

$$2\alpha \log_2\frac{1}{\alpha} \le \mathbf{I}[f],$$

with the left side read as $0$ when $\alpha = 0$.

Equivalently, a set $A \subseteq \{0,1\}^n$ of density $\alpha \le 1/2$ has at least $\alpha \log_2(1/\alpha) \cdot 2^n$ edges leaving it. Equality holds for subcubes (e.g. $\alpha$ a power of $1/2$).

## Proof sketch

Induct on $n$ via the edge-counting form: split $A$ into the two halves $A_0, A_1$ along the last coordinate, with densities $\alpha_0, \alpha_1$. The boundary of $A$ is at least the boundaries of the halves plus $|\alpha_0 - \alpha_1|2^{n-1}$, and the function $\phi(\alpha) = \alpha\log_2(1/\alpha)$ satisfies $\phi(\frac{a+b}2) \le \frac{\phi(a) + \phi(b)}{2} + \frac{|a - b|}{2}$ for $a, b \in [0,1]$, which closes the induction.

## Depends on

- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Edge-isoperimetric inequality](../kahn-kalai-linial-inequality/the-edge-isoperimetric-inequality-and-the-logari/klo-edge-isoperimetric.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
