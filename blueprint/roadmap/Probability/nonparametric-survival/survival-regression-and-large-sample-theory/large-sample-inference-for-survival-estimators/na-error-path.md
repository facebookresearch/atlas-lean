# Nelson–Aalen error path

Fix a real $\tau$ and $K$ grid steps of length $\tau/K$; the grid time $k\tau/K$ is read as $0$ when $K = 0$. The normalized Nelson–Aalen error path is the grid step path in $D([0, \tau])$ with increments $\sqrt n(\Delta\hat A_{i+1} - \Delta\alpha_{i+1})$, $i < K$. For $\tau > 0$ its value at the grid time $k\tau/K$, $k \le K$, is $\sqrt n(\hat A_k - (\alpha_k - \alpha_0))$, so it is the step version of $t \mapsto \sqrt n(\hat A(t) - (\alpha(t) - \alpha(0)))$.
