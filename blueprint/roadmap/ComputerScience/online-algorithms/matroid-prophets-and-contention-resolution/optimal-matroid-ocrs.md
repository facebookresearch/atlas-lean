# Optimal online contention resolution for matroids

Every matroid admits a $\frac12$-selectable OCRS, and $\frac12$ is optimal; moreover every matroid admits a $(1 - 1/e)$-selectable random-order contention resolution scheme, where elements arrive in uniformly random order, and $1 - 1/e$ is optimal.

## Proof sketch

Lee and Singla reduce the design of an OCRS to a matroid prophet inequality against the *ex-ante relaxation* benchmark $\max_{x \in P_{\mathcal{M}}} \sum_e x_e\,\mathbb{E}[X_e \mid \text{top } x_e \text{ quantile}]$, and prove a $\frac12$ prophet inequality against this stronger benchmark via balanced thresholds; LP duality between OCRSs and ex-ante prophet inequalities converts this into a $\frac12$-OCRS. The random-order case uses a time-dependent greedy rule analyzed by a continuous-time argument.

## Depends on

- [Online contention resolution schemes](online-contention-resolution.md)

## Proof depends on

- [Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality](matroid-prophet-half.md)

## Sources

- Euiwoong Lee, Sahil Singla, "Optimal Online Contention Resolution Schemes via Ex-Ante Prophet Inequalities", ESA (2018), arXiv:1806.09251.
