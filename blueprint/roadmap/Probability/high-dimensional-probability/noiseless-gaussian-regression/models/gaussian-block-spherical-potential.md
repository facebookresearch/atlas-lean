# Spherical kernel potential and outgoing posterior laws

Normalize volume on the open Euclidean unit ball and push it forward by $x\mapsto x/\|x\|$, with the native zero fallback, to obtain $\sigma_d$. For $k=\lfloor d/16\rfloor$ set $J_\nu(s)=\int \|u-s\|^{-2k}\,d\nu(u)$ with extended reciprocal and lower integral. The functional is $\Phi(\nu)=D(\nu\Vert\sigma_d)_{\mathbb R}-\int\log(J_\nu(s)_{\mathbb R})\,d\nu(s)$, with the totalized real projections and Bochner integral. Bounded density means domination by $H\sigma_d$ for some positive real $H$. For the block model adjoin $k$ fresh Gaussian rows with exact labels to the signal-state law, weight by each outgoing transition atom, and push forward to the unchanged signal and new state. The posterior of each state is its signal component scaled by inverse total mass; the average of $\Phi$ is weighted by that law’s own component masses.

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L145-L182)
