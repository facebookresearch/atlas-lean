# Continuous Wagner network development and viability

**Model.** A network of $N$ transcription factors is an $N\times N$ real matrix $W = (w_{ij})$ with entries in $[-1,1]$, where $w_{ij}$ is the effect of the product of gene $j$ on the production of gene $i$ (positive for activation, negative for repression). An individual has initial expression vector $S(0)\in[-1,1]^N$ and develops by

$$s_i(t+1) = f\Big(\sum_{j=1}^{N} w_{ij}\,s_j(t)\Big),\qquad f(x) = \frac{2}{1+e^{-a x}} - 1 = \tanh\!\Big(\frac{a x}{2}\Big),$$

with gain $a > 0$; large $a$ recovers Wagner's discrete model with $f(x) = \operatorname{sgn}(x)$, while moderate $a$ (for example $a = 1.5$) gives graded expression levels.

**Viability.** With the normalized squared distance $D(X,Y) = \sum_{i=1}^{N}(X_i-Y_i)^2/(4N) \in [0,1]$ on $[-1,1]^N$, let

$$\varphi(S_t) = \frac{1}{\tau}\sum_{u=t-\tau}^{t} D\big(S(u),\bar S_t\big),$$

where $\bar S_t$ is the mean of the last $\tau$ expression vectors. The individual is viable if $\varphi(S_t) < \sigma$ for some $t \le L_{\max}$; its final state is then an (approximate) fixed point $S^{*} = f(WS^{*})$, and the number of steps taken is the developmental path length. The defaults are $\tau = 10$, $\sigma = 10^{-4}$, $L_{\max} = 100$.

**Diploid mating.** The offspring of networks $W$ and $W'$ has network $(W + W')/2$, the elementwise average.

**Proposition.** $f$ is odd, strictly increasing and maps $\mathbb R$ onto $(-1,1)$ with $|f'(x)| \le a/2$. Consequently, if $\tfrac a2\|W\|_2 < 1$, the developmental map $S \mapsto f(WS)$ is a contraction of $[-1,1]^N$ in the Euclidean norm, so every developmental trajectory converges to the unique fixed point $S^{*} = 0$, and the individual is viable with final state $0$ whenever $L_{\max}$ is large enough for $\varphi$ to fall below $\sigma$; nontrivial stable expression patterns require $\tfrac a2\|W\|_2 \ge 1$.

## Proof sketch

The identity $2/(1+e^{-ax}) - 1 = \tanh(ax/2)$ follows by multiplying numerator and denominator by $e^{ax/2}$, so the map is the standard bounded sigmoidal response and $f'(x) = \tfrac a2\,\mathrm{sech}^2(ax/2) \le a/2$. For the contraction claim, $\|f(Wx)-f(Wy)\| \le \tfrac a2\|W(x-y)\| \le \tfrac a2\|W\|_2\,\|x-y\|$, and the Banach fixed-point theorem gives a unique, globally attracting fixed point, which is $0$ because $f$ is odd. Above this threshold the map can have several fixed points (alternative stable expression states reached from different initial vectors) or periodic orbits, which the viability criterion rejects. In simulations with $a = 1.5$, final expression levels of viable individuals spread over $(-1,1)$ rather than clustering at $\pm 1$, the continuous model yields viable networks more often than the discrete one once networks have more than about seven genes, and averaging two viable networks (diploid mating) produces a viable offspring far more often than drawing a random network of the same size.

## Sources

- M. O. Carneiro, C. H. Taubes and D. L. Hartl, "Model transcriptional networks with continuously varying expression levels", BMC Evolutionary Biology 11 (2011), 363, Background and Methods, Eqs. (1)–(3), and Results and Discussion, <https://doi.org/10.1186/1471-2148-11-363>, PMCID PMC3270072.
