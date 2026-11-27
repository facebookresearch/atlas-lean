# The windowed scattering transform is nonexpansive

If one layer $f \mapsto (A f, (U[\lambda] f)_\lambda)$ is nonexpansive, then summing over all finite paths $p$,

$$\sum_{p} \|A U[p] f - A U[p] h\|^2 \le \|f - h\|^2,$$

that is $\|S_J[P_J] f - S_J[P_J] h\| \le \|f - h\|$ for the windowed scattering $S_J[p] = A_J U[p]$ (S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), Proposition 2.5, equations (27)–(28)). For Mallat's wavelet layer, nonexpansiveness follows from the unitarity of the wavelet transform $W_J$ (Proposition 2.1) and $||a| - |b|| \le |a - b|$. The statement holds for an arbitrary index set $\Lambda$ and arbitrary, possibly nonlinear, maps.
