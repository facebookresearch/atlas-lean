# Combining online algorithms for metrical task systems

Let $\mathcal{A}_0, \dots, \mathcal{A}_{m-1}$, $m \ge 2$, be online algorithms for the same metrical task system, all starting from the same state. For every $\gamma \in (1, 2]$ there is a deterministic online algorithm whose cost on every input with optimal cost at least $1$ is at most $\left(\frac{2\gamma^m}{\gamma - 1} + 1\right)\min_i \mathrm{cost}(\mathcal{A}_i)$; with $\gamma = \frac{m}{m-1}$ the factor is $9$ for $m = 2$ and at most $2em$ in general (inputs with smaller positive optimum are handled by rescaling costs). If the metric has diameter at most $D$, then for every $\varepsilon \in (0, 1/2)$ there is a randomized online algorithm whose expected cost on every input is at most $(1 + \varepsilon)\min_i \mathrm{cost}(\mathcal{A}_i) + O\!\left(\frac{D}{\varepsilon}\right)\ln m$.

## Proof sketch

The deterministic algorithm simulates all $\mathcal{A}_i$ and follows them cyclically in the manner of the $m$-lane cow-path problem: in round $\ell$ it follows $\mathcal{A}_{\ell \bmod m}$ while that algorithm's cost is at most $\gamma^\ell$. A switch from $\mathcal{A}_{i'}$ to $\mathcal{A}_i$ costs, by the triangle inequality through the common start state, at most the current costs of the two algorithms, so round $\ell$ costs at most $\gamma^{\ell-1} + \gamma^\ell$; summing the geometric series against the cost of the best algorithm gives the factor. The randomized algorithm of Blum and Burch treats the algorithms as experts, keeps multiplicative weights $w_i \leftarrow w_i \beta^{c_i/D}$ with $\beta = 1 - 2\varepsilon$, and switches between algorithms by an earth-mover coupling of consecutive weight distributions, so that the expected switching cost is charged to the change of the distribution.

## Depends on

- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)

## Proof depends on

- [Regret of Hedge for losses in the unit interval](../../machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le.md)

## Sources

- Amos Fiat, Yuval Rabani, Yiftach Ravid, "Competitive k-Server Algorithms", Journal of Computer and System Sciences 48(3) (1994).
- Avrim Blum, Carl Burch, "On-Line Learning and the Metrical Task System Problem", Machine Learning 39(1) (2000).
- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144, Theorems 18, 19 and 24.
