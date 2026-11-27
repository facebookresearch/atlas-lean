# Expectation under the p-biased product measure

For $p \in [0, 1]$ the *$p$-biased measure* on $\{0,1\}^n$ gives $x$ probability $p^{|x|}(1 - p)^{n - |x|}$. For a real function $h$ on the cube, $\mathbb{E}_p[h] = \sum_x p^{|x|}(1-p)^{n-|x|}h(x)$ is a polynomial in $p$. Under the identification true $\mapsto -1$, each bit read as $\pm 1$ has mean $\mu = 1 - 2p$ and standard deviation $\sigma = 2\sqrt{p(1-p)}$. For $0 < p < 1$, where $\sigma > 0$, the standardized bit $\phi_i = (x_i - \mu)/\sigma$ is defined and the $p$-biased Fourier coefficient of $h$ on $\{i\}$ is $\mathbb{E}_p[h\,\phi_i]$; at $p \in \{0, 1\}$ the measure is a point mass, $\sigma = 0$ and no standardized basis exists.

## Depends on

- [Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-cube.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
