# Stick-breaking limit of the site frequency spectrum of a Yule population

Use the model and notation of [the site-wise Luria–Delbrück limit](site-wise-luria-delbruck-limit-of-mutant-cell-counts.md). Label cells by $\mathcal{T}=\bigcup_{l\ge0}\{0,1\}^l$ (root $\emptyset$, daughters $x0,x1$). Let $(U_y)$ be uniform on $[0,1]$ with $U_{y0}+U_{y1}=1$ and $(U_{y0})_{y\in\mathcal{T}}$ independent, and put $P_x=\prod_{\emptyset\prec y\preceq x}U_y$. Then $P_x$ is the almost-sure limit, as $t\to\infty$, of the fraction of cells alive at time $t$ that descend from cell $x$.

**Theorem (single-site tail).** For $a\in(0,1)$, as $n\to\infty$ and $n\mu\to\theta\in[0,\infty)$,

$$\mu^{-1}\,\mathbb{P}\bigl[n^{-1}B_i^{n,\mu}>a\bigr]\to 2\,(a^{-1}-1).$$

**Corollary (expected site frequency spectrum).** If also $|\mathcal{S}|\mu\to\eta\in[0,\infty)$, then

$$\mathbb{E}\sum_{i\in\mathcal{S}}\delta_{n^{-1}B_i^{n,\mu}}\bigl((a,1)\bigr)\to 2\eta\,(a^{-1}-1).$$

**Theorem (distributional limit).** As $n\to\infty$, $n\mu\to\theta$ and $|\mathcal{S}|\mu\to\eta\in[0,\infty)$,

$$\sum_{i\in\mathcal{S}}\delta_{n^{-1}B_i^{n,\mu}}\;\longrightarrow\;\sum_{x\in\mathcal{T}\setminus\{\emptyset\}}M_x\,\delta_{P_x}$$

in distribution for the vague topology on measures on $(0,1]$, where $(M_x)$ are i.i.d. $\mathrm{Poisson}(\eta)$ independent of $(P_x)$.

The limit has mean measure $2\eta(a^{-1}-1)$ on $(a,1)$, and its variance on $(a,1)$ is at least $2\eta(a^{-1}-1)$, so the coefficient of variation of the number of sites above frequency $a$ diverges as $a\uparrow1$: high-frequency mutations are dominated by early-division randomness.

## Depends on

- [Site-wise Luria–Delbrück limit of mutant cell counts](site-wise-luria-delbruck-limit-of-mutant-cell-counts.md)

## Expansion

A site reaches a positive frequency only if it mutates in one of the first few divisions. The $r$-th cell born carries a fraction of the eventual population that, conditionally, exceeds $a$ with probability $(1-a)^{r-1}$, and the per-cell mutation probability is about $2\mu$, so summing $2\mu(1-a)^{r-1}$ over $r\ge1$ gives $2\mu/a$; subtracting the root's contribution yields $2\mu(a^{-1}-1)$. Under $|\mathcal{S}|\mu\to\eta$ the number of sites mutating in each early cell is Poisson$(\eta)$, and Pólya-urn (uniform splitting) structure of the Yule tree gives the stick-breaking fractions $P_x$. An infinite-sites approximation is justified by showing that the expected discrepancy between the true counts and the infinite-sites counts on $(a,1)$ vanishes.

## Sources

- D. Cheek, T. Antal, "Genetic composition of an exponentially growing cell population", arXiv:1905.12355 (2019), Section 3.2 (Lemma 3.2), Theorem 4.4, Corollary 4.5, Theorem 4.6, Remarks 4.7–4.8, Section 7, <https://doi.org/10.48550/arXiv.1905.12355>.
