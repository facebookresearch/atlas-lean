# Mean strong stationary time of the multi-type Wright–Fisher diffusion

**Model.** Let $\mathbf{X}$ be the $(d+1)$-type Wright–Fisher diffusion with parent-independent mutation on $\Delta_d = \{\mathbf{x} \in [0,1]^d : \sum_i \mathbf{x}(i) \le 1\}$, generator
$$\mathcal{L} f(\mathbf{x}) = \frac{c}{2} \sum_{i,j=1}^d \mathbf{x}(i)\big(\mathbf{1}\{i=j\} - \mathbf{x}(j)\big)\partial_{ij} f + \theta \sum_{i=1}^d \Big( (1 - \mathbf{x}(i))\boldsymbol{\nu}(i) - \mathbf{x}(i)\sum_{j \ne i} \boldsymbol{\nu}(j)\Big)\partial_i f,$$
where $c = \Lambda(\{0\}) > 0$ (i.e. $\Lambda = c\,\delta_0$), $\theta > 0$ is the total mutation rate, and $\boldsymbol{\nu}$, with $\boldsymbol{\nu}(d+1) = 1 - \sum_{i\le d} \boldsymbol\nu(i)$, is a mutation distribution in the interior of $\Delta_d$.

**Fixation lines.** For $k \in \mathbb{N}_0$ the $k$-th fixation line $F^k$ is the pure-birth chain started at $k$ that jumps $n \to n+1$ at rate $c\binom{n+1}{2} + \theta(n+1)$; let $T_\infty(k)$ be its explosion time.

**Theorem.** $\mathbf{X}^{\mathbf{x}}$ has a strong stationary time $T$ with $T \overset{(d)}{=} T_\infty(0)$, and
$$\mathbb{E}[T] = \frac{2}{c} \sum_{j=1}^\infty \frac{1}{j\,(j - 1 + 2\theta/c)} = \frac{2}{c}\Big(\psi\big(\tfrac{2\theta}{c}\big) + \gamma\Big),$$
where $\psi$ is the digamma function and $\gamma$ the Euler–Mascheroni constant. More generally $\mathbb{E}[T_\infty(k)] = 2\sum_{j > k} \big(c\, j(j-1) + 2 j \theta\big)^{-1}$.

**Mean fixation times without mutation** ($\theta = 0$, $\mathbf{x}$ in the interior). The time $T_{\mathrm{fix},n}^{\mathbf{x}}$ until at most $n$ types remain satisfies
$$\mathbb{E}\big[T_{\mathrm{fix},n}^{\mathbf{x}}\big] = -\frac{2}{c}\sum_{\ell=1}^n (-1)^{n-\ell}\binom{d-\ell}{d-n}\sum_{1 \le c_1 < \cdots < c_\ell \le d+1}\Big(1 - \sum_{j=1}^\ell \mathbf{x}(c_j)\Big)\log\Big(1 - \sum_{j=1}^\ell \mathbf{x}(c_j)\Big).$$
For $n = 1$, $d = 1$ this is the classical mean absorption time $-\frac{2}{c}[x\log x + (1-x)\log(1-x)]$.

## Depends on

- [Order of allele extinctions in the Λ-Wright–Fisher process](order-of-allele-extinctions-in-the-lambda-wright-fisher-process.md)

## Expansion

In the lookdown representation the level-$0$ particle is resampled from $\boldsymbol\nu$ by mutation, and the fixation line started at $0$ tracks the highest level all of whose types descend from post-time-$0$ mutations or the level-$0$ particle. Once it explodes, every level carries a type drawn afresh from the stationary mechanism, independent of the initial state: a strong stationary time. The explosion time is a sum of independent exponential holding times with rates $c\binom{j}{2}\cdot\frac{2}{j}\cdot\frac{j}{2} + \theta j$ summed over $j \ge 1$, giving the digamma series. Fixation times without mutation are explosion times of $F^{m-1}$ at a random level $m$ determined by i.i.d. type labels; inclusion–exclusion over which types are seen produces the log formula.

## Sources

- Airam Blancas, Adrián González Casanova, Sebastian Hummel and Sandra Palau, "Fixation and stationary times for the Λ-Wright-Fisher process", arXiv:2308.09218 (2023), Theorem 1, Proposition 2, Proposition 3(a), Corollary 1(a) and Corollary 2, <https://doi.org/10.48550/arXiv.2308.09218>.
