# The Tribes function

For $w, s \ge 1$, the *Tribes* function $\mathrm{Tribes}_{w,s} : \{0,1\}^{sw} \to \{0,1\}$ is the OR of $s$ ANDs of $w$ bits each, on disjoint blocks (tribes): $\mathrm{Tribes}_{w,s}(x) = \bigvee_{j=1}^s \bigwedge_{i=1}^w x_{j,i}$. It is monotone and $\Pr[\mathrm{Tribes}_{w,s} = 1] = 1 - (1 - 2^{-w})^s$. Choosing $s = s(w)$ largest with $(1 - 2^{-w})^s \ge 1/2$ makes it nearly balanced, with $n = sw \approx 2^w w \ln 2$ variables.

## Depends on

- [Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-cube.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
