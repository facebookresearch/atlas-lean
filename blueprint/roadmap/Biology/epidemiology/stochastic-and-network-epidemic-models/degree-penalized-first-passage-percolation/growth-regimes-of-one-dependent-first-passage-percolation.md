# Growth regimes of degree-penalized first passage percolation on spatial scale-free graphs

**Model.** *Spatial scale-free graphs.* Fix $d \in \mathbb{N}$, a power-law exponent $\tau \in (2,3)$, a long-range parameter $\alpha > 1$ and constants $\overline{c} > \underline{c} > 0$. Vertices are $\mathbb{Z}^d$ (scale-free percolation, SFP) or a unit-intensity Poisson process on $\mathbb{R}^d$ (infinite geometric inhomogeneous random graph, IGIRG). Each vertex $v$ gets an i.i.d. weight $W_v \ge 1$ with $P(W > w) = \ell(w)w^{-(\tau-1)}$, $\ell$ slowly varying. Given positions and weights, each pair $x,y$ is joined independently with probability $h(x-y,W_x,W_y)$, where

$$
\underline{c}\,\min\Bigl\{1, \frac{w_1w_2}{|x|^d}\Bigr\}^{\alpha} \le h(x,w_1,w_2) \le \overline{c}\,\min\Bigl\{1, \frac{w_1w_2}{|x|^d}\Bigr\}^{\alpha}.
$$

*Transmission.* Each edge $xy$ gets the transmission time $\mathcal{C}(xy) = L_{xy}(W_xW_y)^{\mu}$ with penalty strength $\mu > 0$ and $L_{xy}$ i.i.d. with $c_1t^{\beta} \le P(L \le t) \le c_2 t^{\beta}$ for $t \in [0,t_0]$. The cost distance $d_{\mathcal{C}}(x,y)$ is the minimal total cost of a path. This models an infection whose rate of new infections grows only sublinearly with the number of contacts of the spreader (damped superspreading).

Let $\mathcal{C}_\infty$ be the unique infinite component and set

$$
\mu_{\mathrm{expl}} = \frac{3-\tau}{2\beta},\quad \mu_{\log} = \frac{3-\tau}{\beta},\quad \mu_{\mathrm{pol},\alpha} = \frac{\alpha - (\tau - 1)}{d(\alpha-2)},\quad \mu_{\mathrm{pol}} = \frac1d + \frac{3-\tau}{\min\{\beta, d(\alpha-2)\}},
$$

$$
\Delta_0 = \frac{1}{1 - \log_2\bigl(\min\{\alpha, \tau - 1 + \mu\beta\}\bigr)}, \qquad
\eta_0 = \begin{cases} 1, & \mu > \mu_{\mathrm{pol}},\\ \min\{d(\mu - \mu_{\log}),\ \mu/\mu_{\mathrm{pol},\alpha}\}, & \mu \le \mu_{\mathrm{pol}}.\end{cases}
$$

**Statement.** For $\mu > \mu_{\mathrm{expl}}$ (below it the process is explosive: transmission times between far-apart vertices stay tight) and every $\varepsilon > 0$:

1. *Polylogarithmic regime.* If $\alpha \in (1,2)$ or $\mu \in (\mu_{\mathrm{expl}}, \mu_{\log})$, then

    $$
    \lim_{|x|\to\infty} P\bigl(d_{\mathcal{C}}(0,x) \le (\log|x|)^{\Delta_0 + \varepsilon} \,\big|\, 0,x \in \mathcal{C}_\infty\bigr) = 1.
    $$

2. *Polynomial regime.* If $\alpha > 2$ and $\mu > \mu_{\log}$, then

    $$
    \lim_{|x|\to\infty} P\bigl(d_{\mathcal{C}}(0,x) \le |x|^{\eta_0 + \varepsilon} \,\big|\, 0,x \in \mathcal{C}_\infty\bigr) = 1,
    $$

    and, together with the companion lower bound, $|x|^{\eta_0 - \varepsilon} \le d_{\mathcal{C}}(0,x)$ with probability tending to one. Hence for $\mu \in (\mu_{\log}, \mu_{\mathrm{pol}})$ transmission times grow polynomially but strictly sublinearly ($\eta_0 < 1$), and for $\mu > \mu_{\mathrm{pol}}$ as $|x|^{1+o(1)}$ (the bounds give $|x|^{1\pm\varepsilon}$ for every $\varepsilon>0$).

3. The same upper bounds hold on the finite graph in a box of volume $n$, for two uniform vertices of the largest component, as $n \to \infty$.

So, as the degree penalty $\mu$ grows, the epidemic passes through four universal phases: explosive, polylogarithmic, strictly polynomial, and essentially linear ($|x|^{1+o(1)}$) in Euclidean distance. This gives one mechanism under which an epidemic on a fixed network can show either exponential-type or polynomial growth, depending only on how strongly high-degree individuals reduce their per-contact transmission.

## Expansion

Upper bounds come from explicit cheap paths. In the polylogarithmic phase a path from $0$ to $x$ uses one long edge of length of order $|x|$, either between low-weight vertices (when $\alpha < 2$) or between two vertices of weight about $|x|^{d/2}$ located at distance $|x|^{(\tau - 1 + \mu\beta)/2 + o(1)}$ from the endpoints and carrying constant cost; iterating this bridge construction on the two shorter remaining gaps gives the exponent $\Delta_0$. In the polynomial phase every long edge near the endpoints has cost polynomial in its length, and optimizing the weights of the bridge endpoints against $P(L \le t) \approx t^{\beta}$ gives $|x|^{d(\mu - \mu_{\log})}$, while rare very long edges give $|x|^{\mu/\mu_{\mathrm{pol},\alpha}}$. A multi-round exposure of the edges and pseudorandom nets of vertices make these hierarchical paths exist with high probability.

## Sources

- Júlia Komjáthy, John Lapinskas, Johannes Lengler and Ulysse Schaller, "Four universal growth regimes in degree-dependent first passage percolation on spatial random graphs", Forum of Mathematics, Sigma 14 (2026), e22, <https://doi.org/10.1017/fms.2025.10161>; numbering as in arXiv:2309.11840: Definitions 1.1–1.2, Theorems 1.4, 1.6, 1.9 and Corollary 1.7.
