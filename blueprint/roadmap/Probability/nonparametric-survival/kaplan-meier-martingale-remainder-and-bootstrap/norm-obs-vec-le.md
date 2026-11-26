# Norm bound for the indicator encoding of an observation

Let $t_0, \dots, t_{k-1}$ be real numbers and, for an observation $o = (T, \delta) \in \mathbb R \times \mathbb R$, let $\mathrm{enc}_t(o) \in \mathbb R^{2k}$ be its indicator encoding, with death coordinates $\mathbf 1\{o = (t_j, 1)\}$ and at-risk coordinates $\mathbf 1\{t_j \le T\}$. Then for every grid $t$ and every observation $o$, the Euclidean norm satisfies

$$\|\mathrm{enc}_t(o)\| \le \sqrt{2k},$$

where $2k$ is the number of coordinates. See the [encoding](obs-vec.md).
