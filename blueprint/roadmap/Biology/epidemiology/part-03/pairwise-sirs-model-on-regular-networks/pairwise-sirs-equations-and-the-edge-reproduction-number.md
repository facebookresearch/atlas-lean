# Pairwise SIRS equations and the edge reproduction number

**Model.** On a network in which every node has degree $n > 2$, nodes are susceptible, infected or recovered; infection passes along each $S$–$I$ edge at rate $\beta$, infected nodes recover at rate $\gamma$ and recovered nodes lose immunity at rate $\epsilon$. Let $[X]$ be the fraction of nodes in state $X$ and $[XY]$ the correspondingly normalized number of edges (edges between equal states counted twice). The node equations are $[S]' = -\beta[SI] + \epsilon(1 - [S] - [I])$, $[I]' = \beta[SI] - \gamma[I]$; edge equations involve triples $[XYZ]$, closed by the pair approximation

$$[XYZ] \approx \frac{n-1}{n}\,\frac{[XY][YZ]}{[Y]} .$$

Using the degree constraints $[SS] + [SI] + [SR] = n[S]$, $[SI] + [II] + [IR] = n[I]$, the closed system is

$$\begin{aligned}
[S]' &= -\beta[SI] + \epsilon(1 - [S] - [I]), \qquad [I]' = \beta[SI] - \gamma[I],\\
[SS]' &= 2\epsilon(n[S] - [SS] - [SI]) - 2\beta\tfrac{n-1}{n}\tfrac{[SS][SI]}{[S]},\\
[SI]' &= -(\gamma + \beta)[SI] + \epsilon(n[I] - [SI] - [II]) + \beta\tfrac{n-1}{n}\tfrac{[SS][SI] - [SI]^2}{[S]},\\
[II]' &= 2\beta[SI] - 2\gamma[II] + 2\beta\tfrac{n-1}{n}\tfrac{[SI]^2}{[S]} .
\end{aligned}$$

It is well posed on the forward-invariant convex set $\{0 \le [S] + [I] \le 1,\ 0 \le [SS] + [SI] \le n[S],\ 0 \le [SI] + [II] \le n[I]\}$.

**Thresholds.** For $\epsilon \to 0$, the pairwise SIR threshold is $\mathcal{R}_0 = \beta(n-2)/\gamma$, equivalently

$$\mathcal{R}_1 = \frac{\beta(n-1)}{\beta + \gamma} \lessgtr 1 \iff \beta(n-2) \lessgtr \gamma .$$

For $\epsilon > 0$, the next-generation matrix on $([SI], [II]/2, [IR])$ at the disease-free state $(1, 0, n, 0, 0)$ gives the **edge reproduction number**

$$\mathcal{R}_1 = \frac{\beta(n-1)(\gamma + \epsilon)}{\gamma(\gamma + \beta + \epsilon)} .$$

**Equilibria.** For small $\epsilon > 0$ and $\mathcal{R}_0 > 1$ there are exactly two relevant equilibria: the disease-free state $([S],[I],[SS],[SI],[II]) = (1, 0, n, 0, 0)$, which is unstable, and an endemic state with

$$[S] = \frac{(n-1)(\gamma + \beta)}{(n^2 - n - 1)\beta - \gamma} + O(\epsilon), \qquad [I] = \epsilon\,\frac{n((n-2)\beta - \gamma)}{\gamma((n^2-n-1)\beta - \gamma)} + O(\epsilon^2) .$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

$\mathcal{R}_1$ counts $SI$ edges produced by one $SI$ edge in a susceptible network: the edge becomes $II$ (infection) with probability $\beta/(\beta+\gamma)$, creating $n - 1$ new $SI$ edges at the newly infected node. With waning immunity the original edge, after passing through $IR$, returns to $SI$ with probability $\epsilon/(\epsilon + \gamma)$ and starts again, because the pair approximation forgets earlier infections of the neighbourhood; solving $\mathcal{R}_1 = \frac{\beta}{\beta+\gamma}\big(n - 1 + \frac{\epsilon}{\epsilon + \gamma}\mathcal{R}_1\big)$ gives the formula. Hence on networks, unlike homogeneous mixing, the SIRS and SIR thresholds differ. Approximating edges by $[XY] \approx n[X][Y]$ (first-order closure) instead loses the network structure and reduces the model to the mean-field SIRS with transmission $n\beta$. The term $[SI]/[S]$ is bounded by $n$ on the invariant set, so the apparent singularity at $[S] = 0$ is harmless.

## Sources

- H. Jardón-Kojakhmetov, C. Kuehn, A. Pugliese, M. Sensi, "A geometric analysis of the SIRS epidemiological model on a homogeneous network", Journal of Mathematical Biology (2021), equations (1)–(10), Lemma 1, Proposition 1 with equations (11)–(12), Remark 2, Lemma 2 and Proposition 4 with equation (31), <https://doi.org/10.1007/s00285-021-01664-5>.
