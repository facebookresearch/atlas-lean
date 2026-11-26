# Producer–grazer model with costly feeding effort

**Model.** Let $x$ be producer biomass and $y$ grazer biomass (in carbon units). Total phosphorus $P$ is conserved; the producer has minimal phosphorus quota $q$, the grazer a fixed phosphorus-to-carbon ratio $\theta$, so free phosphorus available to producers is $P - \theta y$. With maximal producer growth rate $b$, light-limited carrying capacity $K$, maximal conversion efficiency $\hat e$, grazer loss rate $d$, feeding effort $\xi > 0$ carrying an energetic cost $\xi$, and Holling type II ingestion $f(x) = \mu \xi x / (1 + \mu \xi \tau x)$ (encounter rate $\mu$, handling time $\tau$), the base model (System 1) is

$$\frac{dx}{dt} = b x \min\Big(1 - \frac{x}{K},\ 1 - \frac{x}{(P - \theta y)/q}\Big) - f(x) y,$$

$$\frac{dy}{dt} = \hat e \min\Big(1, \frac{(P - \theta y)/x}{\theta}\Big) f(x) y - \xi y - d y .$$

Let $k = \min(K, P/q)$.

**Theorem 1 (invariant region).** Solutions starting in the open rectangle $\Delta = \{0 < x < k,\ 0 < y < P/\theta\}$ remain in $\Delta$ for all $t \ge 0$.

**Theorem 2.** The extinction equilibrium $E_0 = (0, 0)$ is a saddle with eigenvalues $b$ and $-(\xi + d)$, hence unstable.

**Theorem 3.** The grazer-extinction equilibrium $E_1 = (k, 0)$ is locally asymptotically stable if

$$G(k, 0) = \hat e \min\Big(1, \frac{P}{k\theta}\Big) \frac{\mu \xi k}{1 + \mu \xi \tau k} - \xi - d < 0 .$$

**Adaptive effort (Theorems 4–6).** If $\xi$ evolves by gradient dynamics $\dot\xi = v H(x, y, \xi)$ confined to $[\xi_{\min}, \xi_{\max}]$, the box $\{0 < x < k,\ 0 < y < P/\theta,\ \xi_{\min} \le \xi \le \xi_{\max}\}$ is forward invariant, $(0, 0, \xi^*)$ is always unstable, and $(k, 0, \xi^*)$ is stable when $G(k, 0, \xi^*) < 0$ together with a sign condition on $\partial_\xi H$ at that point.

## Expansion

The two arguments of the minimum express energy (light) limitation and phosphorus limitation of the producer; the grazer's efficiency drops when food phosphorus per carbon $(P - \theta y)/x$ falls below its own requirement $\theta$. Invariance follows by checking each side of the rectangle: near $x = 0$ the producer equation is bounded below by $\delta x$, so $x$ stays positive; $x$ cannot exceed $k$ because growth turns negative there; $y$ cannot reach $P/\theta$ because the grazer would have used all phosphorus and its conversion term vanishes. At $(k, 0)$ the Jacobian is triangular, and $G(k, 0)$ is the per-capita growth rate of a rare grazer on a producer at carrying capacity, so negativity means the grazer cannot invade. Adaptive feeding effort can rescue the grazer under poor food quality, while fast adaptation can enlarge limit-cycle amplitudes.

## Sources

- O. Oladepo, A. Peace, "Nutrient-driven adaptive evolution of foraging traits impacts producer-grazer dynamics", Bulletin of Mathematical Biology 87 (2025) 102, System (1), Equations (8)–(13), Theorems 1–6, <https://doi.org/10.1007/s11538-025-01482-6> (PMC12198312).
