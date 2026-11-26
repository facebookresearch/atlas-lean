# Exact AIC network selection by pruning nested cytokine models

**Model.** For cytokines $i = 1, \dots, K$ with concentrations $x_i(t)$, $x_i(0) = 0$, the secretion rate under a stimulus of strength $s_i$ is

$$\frac{dx_i}{dt} = y_i(t) = s_i \prod_u \big(1 + \alpha_{u,i}x_u(t)\big) \prod_v \frac{1}{1 + \beta_{v,i}x_v(t)},$$

with $\alpha_{u,i} \ge 0$ (up-regulation of $i$ by $u$) and $\beta_{v,i} \ge 0$ (down-regulation), never both positive for the same pair. A network configuration is the set of non-zero edge parameters. With log-normal measurement error of known standard deviation $\sigma_i$, the likelihood of measured rates $\hat y_{i,j}$ is $L(\theta) = \prod_{i,j}(2\pi\sigma_i^2)^{-1/2}\exp\big(-(\log_{10}y_{i,j} - \log_{10}\hat y_{i,j})^2/(2\sigma_i^2)\big)$, and for a configuration $S$ with $|S|$ edges

$$D(S) = \min_\theta\, -2\log L(\theta), \qquad \mathrm{AIC}(S) = D(S) + 2|S|.$$

Candidate edges are restricted to the set $O$ of $N$ edges whose blocking produced a statistically significant change, so there are $2^N$ configurations instead of $3^{K^2}$.

**Monotonicity.** If $S_i \subseteq S_j$ then $D(S_i) \ge D(S_j)$, since the smaller model is the larger one with some edge parameters fixed at $0$.

**Pruning lemmas.** Let $S_{\mathrm{sel}}$ be the configuration with smallest AIC found so far, with $n_s$ edges, and for size $n$ set $D^n_{\mathrm{thr}} = D(S_{\mathrm{sel}}) + 2(n_s - n)$; an $n$-edge configuration beats or ties $S_{\mathrm{sel}}$ iff $D(S_n) \le D^n_{\mathrm{thr}}$. Let $S^n_{\mathrm{init}}$ be the $n$ edges with the largest fitted weights in the full model. A non-empty $S' \subseteq S^n_{\mathrm{init}}$ is *essential* if $D(O \setminus S') \ge D^n_{\mathrm{thr}}$.
1. If $S'$ is essential, no configuration $W \subseteq O \setminus S'$ has $D(W) < D^n_{\mathrm{thr}}$.
2. If $S'$ is essential and $S' \subseteq S'' \subseteq S^n_{\mathrm{init}}$, then $S''$ is essential.

Every $n$-edge configuration has the form $R \cup (S^n_{\mathrm{init}} \setminus S')$ with $|R| = |S'|$ and $R \subseteq O \setminus S^n_{\mathrm{init}}$, so a search over $n = 1, \dots, N-1$ that skips every configuration avoiding an essential set, and updates $S_{\mathrm{sel}}$ whenever an improvement is found, terminates with the configuration of minimal AIC among all subsets of $O$.

## Expansion

Lemma 1 is monotonicity applied twice: $W \subseteq O \setminus S'$ gives $D(W) \ge D(O \setminus S') \ge D^n_{\mathrm{thr}}$. Lemma 2 follows from $O \setminus S'' \subseteq O \setminus S'$. Because removing a set that is essential certifies that every configuration missing it is too poor, and essentiality is inherited by supersets, the search can enumerate small candidate removal sets first and prune whole families of configurations by fitting only the models $O \setminus S'$. The thresholds also shrink whenever a better configuration is found. In a three-cytokine example with edges A $\to$ B, B $\dashv$ C and a spurious A $\dashv$ C, the full model fits best but AIC selects the true two-edge network. Direct interactions are defined relative to the measured cytokines: an effect mediated by an unmeasured cytokine appears as a direct edge.

## Sources

- J. E. Jansen, D. Aschenbrenner, H. H. Uhlig, M. C. Coles, E. A. Gaffney, "A method for the inference of cytokine interaction networks", PLoS Computational Biology 18(6) (2022) e1010112, Eqs. (1)–(6), Definitions 1–4, Remarks 1–3, Lemmas 1–2 and Procedure Ω, <https://doi.org/10.1371/journal.pcbi.1010112>, PMCID PMC9216621.
