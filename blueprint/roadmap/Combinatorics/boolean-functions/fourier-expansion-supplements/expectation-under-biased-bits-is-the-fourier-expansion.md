# Expectation under independent biased bits is the Fourier expansion at the means

For a real function $f$ on $\{-1,1\}^n$ and $\mu \in [-1,1]^n$, let $x$ have independent coordinates with $\mathbb{E}[x_i] = \mu_i$. Then

$$\mathbb{E}[f(x)] = \sum_{S \subseteq [n]} \hat f(S) \prod_{i \in S} \mu_i,$$

i.e. the expectation is the multilinear (Fourier) polynomial of $f$ evaluated at $\mu$. The identity holds formally for every real $\mu$ when the probability weights $\prod_i (1 + x_i \mu_i)/2$ are used as signed weights.

## Proof sketch

By linearity it suffices to check characters: $\mathbb{E}[\chi_S(x)] = \prod_{i \in S}\mathbb{E}[x_i] = \prod_{i\in S}\mu_i$ by independence.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)

## Proof depends on

- [Fourier inversion on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/sum-bool-fourier-coeff-mul-cube-chi.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
