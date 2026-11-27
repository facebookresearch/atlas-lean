# Meeting, coalescence and voter-model consensus times on the directed configuration model

**Setting.** The directed configuration model $\mathrm{DCM}(\mathbf{d}^+,\mathbf{d}^-)$ on $[n]$ matches out-half-edges to in-half-edges uniformly at random for prescribed out- and in-degrees with $m = \sum_x d^+_x = \sum_x d^-_x$ edges. Assume $2 \le d^+_{\min}$ and $d^+_{\max}, d^-_{\max} \le C$. A continuous-time random walk jumps at rate $1$ along a uniformly chosen out-edge; in the dual voter model, each vertex at rate $1$ adopts the opinion at the other end of a uniformly chosen out-edge; $\pi$ is its stationary law. Coalescing random walks start one walker per vertex and merge on meeting; the voter model is their dual, with $\tau_{\mathrm{coal}}$ the time to a single walker and $\tau_{\mathrm{cons}}$ the time to consensus. Define

$$\delta = \frac mn,\quad \beta = \frac1m\sum_x (d^-_x)^2,\quad \rho = \sum_x \frac{d^-_x}{m}\frac{1}{d^+_x},\quad \gamma = \sum_x \frac{d^-_x}{m}\frac{d^-_x}{d^+_x},$$

$$\mathfrak{p} = \frac1\delta\Big(\frac{\gamma-\rho}{1-\rho} + \beta - 1\Big),\quad \mathfrak{q} = \Big(1 + (\beta-1)\frac{1-\rho}{\gamma-\rho}\Big)^{-1},\quad \mathfrak{r} = \frac{\rho}{\rho - \mathfrak{q}(1 - \sqrt{1-\rho})},\quad \vartheta = \frac{\mathfrak{r}}{\mathfrak{p}}.$$

**Theorem (meeting time).** For $G$ sampled from the DCM, the meeting time of two independent stationary walks satisfies

$$d_W\Big(\frac{\tau^{\pi\otimes\pi}_{\mathrm{meet}}}{\tfrac12\vartheta n},\ \mathrm{Exp}(1)\Big) \xrightarrow{\ \mathbb{P}\ } 0,$$

where $d_W$ is the $L^1$-Wasserstein distance; in particular the expected meeting time is $\sim \tfrac12\vartheta n$, linear in $n$.

**Corollary (coalescence and consensus).** With independent $Z_k \sim \mathrm{Exp}\binom k2$,

$$d_W\Big(\frac{\tau_{\mathrm{coal}}}{\tfrac12\vartheta n},\ \sum_{k\ge2}Z_k\Big) \xrightarrow{\mathbb{P}} 0,\qquad d_W\Big(\frac{\tau_{\mathrm{cons}}}{\tfrac12\vartheta n},\ \sum_{k\ge K}Z_k\Big) \xrightarrow{\mathbb{P}} 0$$

for the voter model started from i.i.d. $\mathrm{Bernoulli}(u)$ opinions, where $K \sim U A + (1-U)B$ with $U \sim \mathrm{Bern}(u)$, $A \sim \mathrm{Geom}(1-u)$, $B \sim \mathrm{Geom}(u)$ independent of the $Z_k$. Thus coalescing walks on the DCM behave like a time-changed Kingman coalescent.

**Examples.** For $d$-regular in- and out-degrees, $\vartheta = \sqrt{d/(d-1)} \in (1,\sqrt2]$. If all out-degrees equal $d$, $\vartheta = \sqrt{d(d-1)}/(\beta - 1) \le \sqrt{d/(d-1)}$; for Eulerian degree sequences ($d^+_x = d^-_x$), $\vartheta = \big(\beta/\delta - 1 + \sqrt{1 - 1/\delta}\big)^{-1}$.

## Expansion

Oliveira's mean-field theorem says that when $t_{\mathrm{mix}}\,\pi_{\max}\log^5 n \to 0$, coalescence and consensus times divided by the expected stationary meeting time converge to the Kingman-type sums above; on the DCM the mixing time is $O(\log n)$ with cutoff at the entropic time and $\pi_{\max} \le n^{-1+\varepsilon}$, so this applies. The meeting time of two walks is the hitting time of the diagonal by the product chain; by a first-visit-time lemma it is approximately exponential with mean $\big(\pi\otimes\pi(\text{diagonal})\big)^{-1}$ times the expected number of returns to the diagonal in a short window. The first factor is $n\sum_x\pi(x)^2 \approx \mathfrak{p}$, computed from the local tree-like structure of in-neighborhoods, and the return factor $\approx \mathfrak{r}$ accounts for walks that meet and quickly re-meet through short directed loops in the local tree.

## Sources

- Luca Avena, Federico Capannoli, Rajat Subhra Hazra and Matteo Quattropani, "Meeting, coalescence and consensus time on random directed graphs", Ann. Appl. Probab. 34 (2024), 4940–4997, <https://doi.org/10.1214/24-AAP2087>. Numbering follows the arXiv version, arXiv:2308.01832 (2023): Theorems 2.1–2.2 (after Oliveira), Assumption and definitions of Section 3, Theorem 3.1, Corollaries 3.2–3.6, Theorems 4.3–4.4 and Propositions 5.2–5.3, <https://doi.org/10.48550/arXiv.2308.01832>.
