# Fourier coefficients and influences of Tribes

Read $\mathrm{Tribes}_{w,s}$ as a $\pm1$ function with true $\mapsto -1$. Its coefficient on $\emptyset$ is $2(1 - 2^{-w})^s - 1$, and on a nonempty set $T$ meeting exactly $k$ tribes it is $2(-1)^{k + |T|}2^{-kw}(1 - 2^{-w})^{s - k}$. Every coordinate has influence $2^{-(w-1)}(1 - 2^{-w})^{s-1}$; for the nearly balanced choice of $s$ this is $\Theta(\log n / n)$ and the total influence is $\Theta(\log n)$, so Tribes shows that the KKL theorem is tight.

## Proof sketch

Bit $i$ of tribe $j$ is pivotal iff the other bits of tribe $j$ are true and every other tribe has a false bit; these events concern different tribes and are independent. The Fourier formula follows by expanding the product $\prod_j (1 - \mathrm{AND}_j)$ in the Fourier basis.

## Depends on

- [The Tribes function](the-tribes-function.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Proof depends on

- [Kahn–Kalai–Linial inequality](../kahn-kalai-linial-inequality/the-kkl-inequality-statement-and-elementary-boun/kkl-inequality-max.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- J. Kahn, G. Kalai and N. Linial, "The Influence of Variables on Boolean Functions", FOCS 1988.
