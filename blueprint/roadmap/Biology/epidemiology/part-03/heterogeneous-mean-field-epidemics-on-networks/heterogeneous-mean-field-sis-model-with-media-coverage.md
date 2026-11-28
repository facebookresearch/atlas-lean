# Heterogeneous mean-field SIS model with media coverage

**Model.** On an uncorrelated network with degree distribution $p(k)$, $k = 1, \dots, n$, mean degree $\langle k \rangle$ and $N$ nodes, let $i_k(t) \in [0, 1]$ be the infected fraction of degree-$k$ nodes and

$$\Theta(t) = \frac{1}{\langle k\rangle}\sum_{k=1}^{n} k\, p(k)\, i_k(t)$$

the probability that a random edge points to an infected node. A media variable $M(t) \ge 0$ grows with prevalence and reduces transmission of a degree-$k$ node by the saturating factor $P(M, k) = kM/(a + kM)$:

$$i_k' = \beta \big(1 - P(M, k)\big) k (1 - i_k)\Theta - \mu i_k, \qquad M' = m_0 + \omega N \sum_{k} p(k) i_k - \lambda M,$$

with $\beta, \mu, a, \omega, \lambda > 0$ and baseline coverage $m_0 \ge 0$. The box $\prod_k [0, 1] \times [m_0/\lambda, (m_0 + \omega N)/\lambda]$ attracts all solutions, and $E_0 = (0, \dots, 0, m_0/\lambda)$ is the unique disease-free equilibrium.

**Theorem.** Let

$$R_0 = \frac{a\beta\lambda}{\mu \langle k\rangle} \sum_{k=1}^{n} \frac{k^2 p(k)}{a\lambda + k m_0}.$$

1. If $R_0 < 1$, $E_0$ is locally and globally asymptotically stable; if $R_0 > 1$, it is unstable.
2. For $m_0 = 0$, $R_0 = \beta\langle k^2\rangle/(\mu\langle k\rangle)$, the classical heterogeneous mean-field SIS threshold; media coverage driven only by current prevalence ($\omega$) never changes the threshold.
3. For $m_0 > 0$, $R_0 < a\beta\lambda/(\mu m_0)$ for every degree distribution, so baseline coverage restores a finite epidemic threshold even on scale-free networks whose second moment $\langle k^2\rangle$ diverges with $n$; $R_0$ is decreasing in $m_0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At $E_0$, with $M_0 = m_0/\lambda$, the new-infection Jacobian is $F_{kj} = \beta\, \frac{a k}{a + k M_0}\, \frac{j p(j)}{\langle k\rangle}$ and $V = \mu\,\mathrm{Id}$. $F$ has rank one, $F = u v^{\top}$, so $\rho(F V^{-1}) = v^{\top} u/\mu$, which is the displayed sum. For global stability, $M' \ge m_0 - \lambda M$ gives $\liminf M \ge M_0$, so for any $\varepsilon > 0$ eventually $i_k' \le \beta \frac{a k}{a + k(M_0 - \varepsilon)}\Theta - \mu i_k$; the comparison linear system is cooperative with rank-one next-generation matrix of spectral radius $R_0(M_0 - \varepsilon)$, below $1$ for small $\varepsilon$, so every $i_k \to 0$ and then $M \to M_0$. Item 3 uses $k^2/(a\lambda + k m_0) < k/m_0$. The source's global-stability argument compares with the media-free system and asserts $\beta\langle k^2\rangle/(\mu\langle k\rangle) \le 1$ from $R_0 < 1$, which does not follow when $m_0 > 0$; the comparison through $\liminf M \ge M_0$ written above closes that gap. Items 2–3 recover the observation that, on Barabási–Albert networks, the media-free model has no positive threshold.

## Sources

- Y. Wang, J. Cao, Z. Jin, H. Zhang, G.-Q. Sun, "Impact of media coverage on epidemic spreading in complex networks", *Physica A* 392(23) (2013) 5824–5835, Section 2 (model (1)–(2)), Section 3.1 ($R_0$, Remark 1, Theorems 1–2); item 3 and the corrected comparison step are derived here. <https://doi.org/10.1016/j.physa.2013.07.067> (PMC7185856).
