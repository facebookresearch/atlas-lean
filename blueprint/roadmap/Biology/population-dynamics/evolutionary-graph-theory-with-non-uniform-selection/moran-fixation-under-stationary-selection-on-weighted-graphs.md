# Moran fixation under stationary selection on weighted graphs

**Model (microscopic spatial Moran process).** Let $G$ be a strongly connected directed graph on $n$ vertices with stochastic weight matrix $W$ and let $\pi$ be its unique positive normalised left eigenvector, $\pi W = \pi$. Each vertex is a wild type ($0$) or a mutant ($1$) of relative fitness $r > 0$; write $x \in \{0,1\}^n$ for the configuration and $\zeta = x\mu^{\top}$. At each step, given a **selection policy** $\mu$ (a probability vector on vertices):
- a vertex $v$ is chosen to reproduce with probability $r\mu(v)/(1 + (r-1)\zeta)$ if it is a mutant and $\mu(v)/(1 + (r-1)\zeta)$ if it is a wild type;
- independently a vertex $v'$ is chosen with probability $W(v, v')$ and replaced by a copy of $v$.

Selection is **stationary** if $\mu = \pi$; uniform selection on a doubly stochastic (isothermal) $W$ is the special case of the classical isothermal theorem. Let $T_{\mathrm{fix}}$ be the hitting time of the all-mutant state.

**Theorem (stationary selection).** If $\mu = \pi$, then for every initial distribution concentrated on configurations with $i$ mutants, $0 < i < n$,

$$\mathbb{P}(T_{\mathrm{fix}} < \infty) = \varrho_i = \begin{cases} \dfrac{1 - r^{-i}}{1 - r^{-n}} & r \neq 1,\\[2mm] \dfrac{i}{n} & r = 1,\end{cases}$$

the fixation probability of the classical Moran process, whatever the graph and whatever the positions of the initial mutants.

**Theorem (no alternative).** For any policy $\mu$, with $W_\mu = \mathrm{diag}(\mu)W$, the probabilities that the mutant count goes up or down in one step from $x$ are

$$p_\mu^+(x) = \frac{r\,(xW_\mu\mathbf 1^{\top} - xW_\mu x^{\top})}{1 + (r-1)x\mu^{\top}}, \qquad p_\mu^-(x) = \frac{(1-x)W_\mu x^{\top}}{1 + (r-1)x\mu^{\top}},$$

and the ratio $p_\mu^-/p_\mu^+$ is constant over all configurations iff $\mu = \pi$, in which case it equals $1/r$.

So the projection of the spatial process onto the number of mutants is not Markov in general, which is the gap in the original proof of the isothermal theorem, but under stationary selection the up/down ratio is configuration-free and the mutant count is a martingale-type random walk with the Moran ratio $1/r$. For non-stationary policies, fixation can still equal the Moran value for special initial laws (explicit families on $2$- and $3$-vertex graphs).

## Expansion

Under $\mu = \pi$, $xW_\pi\mathbf 1^{\top} - xW_\pi x^{\top} = \sum_{v \in x,\,v' \notin x}\pi(v)W(v,v')$ is the $\pi$-weighted flow from mutants to wild types, and $(1-x)W_\pi x^{\top}$ is the flow back; stationarity of $\pi$ for $W$ makes the two flows equal for every cut, so $p^-/p^+ = 1/r$ identically. Then $r^{-(\text{number of mutants})}$ is a martingale up to absorption, and optional stopping gives the Moran formula without needing the projection to be Markov.

## Sources

- Peter Keller and Mert Ugurlu, "Fixation probability in Moran-like Processes on graphs", arXiv:2403.12598 (2024), Definition of the microscopic spatial Moran process (Section 2), Theorems 2.1, 3.1 and 3.2, Corollaries 3.1–3.2, Propositions 4.1–4.2, <https://doi.org/10.48550/arXiv.2403.12598>.
