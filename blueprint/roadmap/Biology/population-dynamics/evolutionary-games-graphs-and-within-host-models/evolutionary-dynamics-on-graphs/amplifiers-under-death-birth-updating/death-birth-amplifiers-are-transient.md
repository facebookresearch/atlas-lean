# All death-Birth amplifiers are transient

Let $G_N$ be a non-complete population structure on $N$ vertices (edges possibly directed and
weighted, no self-loops), and let $K_N$ be the unweighted complete graph on $N$ vertices, whose
death-Birth fixation probability is

$$\rho_{\mathrm{dB}}(K_N, r) = \Bigl(1 - \frac{1}{N}\Bigr)\,\frac{1 - 1/r}{1 - 1/r^{\,N-1}}
\qquad (r \ne 1).$$

Then there is a threshold $r^\star > 1$, which may be taken to be $r^\star = 2N^2$, such that

$$\rho_{\mathrm{dB}}(G_N, r) \ <\ \rho_{\mathrm{dB}}(K_N, r) \qquad \text{for all } r > r^\star .$$

Hence no non-complete structure amplifies selection for all $r > 1$: under death-Birth updating
every amplifier is transient, and the only structures that could amplify universally are weighted
versions of the complete graph.

## Depends on

- [Fixation bound from the average out-degree](fixation-bound-from-average-out-degree.md)

## Proof depends on

- [Fixation probability in a frequency-dependent Moran process](../../../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)

## Proof sketch

As $r \to \infty$ the complete-graph value $\rho_{\mathrm{dB}}(K_N, r)$ tends to $1 - 1/N$, while
the out-degree bound caps $\rho_{\mathrm{dB}}(G_N, r)$ at $d/(d+1)$ with $d < N - 1$ for a
non-complete structure, and $d/(d+1) < 1 - 1/N$ in that case. Making the comparison quantitative in
$N$ yields the explicit threshold $r^\star = 2N^2$.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee, M. A. Nowak, "Limits on amplifiers of natural selection under
  death-Birth updating", PLoS Computational Biology 16 (2020) e1007494, Theorem 1 and Eq. (2),
  <https://doi.org/10.1371/journal.pcbi.1007494> (PMC6968837).
