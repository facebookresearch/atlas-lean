# Stable influences are bounded by powers of influences

For every $f : \{-1,1\}^n \to \{-1,1\}$, coordinate $i$ and $0 \le \rho \le 1$,

$$\mathbf{Inf}^{(\rho)}_i[f] \le \mathbf{Inf}_i[f]^{2/(1 + \rho)}.$$

## Proof sketch

$D_i f$ takes values in $\{0, \pm 1\}$ with $\Pr[D_i f \ne 0] = \mathbf{Inf}_i[f]$; by hypercontractivity $\mathrm{Stab}_\rho[g] = \|T_{\sqrt\rho}g\|_2^2 \le \|g\|_{1+\rho}^2 = \mathbb{E}|g|^{1+\rho}$ to the power $2/(1+\rho)$, which for $g = D_i f$ equals $\mathbf{Inf}_i[f]^{2/(1+\rho)}$.

## Depends on

- [Stable influence and total stable influence](stable-influence.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Proof depends on

- [Bonami–Beckner hypercontractive inequality](../kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-hypercontractivity-general.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
