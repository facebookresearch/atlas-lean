# Airy amplitude of maximal and total tree-child network counts

**Setting.** Let $T_{n,k}$ count binary tree-child networks with $n$ labelled leaves and $k$ reticulations (root of out-degree one), let $M_n=T_{n,n-1}$ be the maximally reticulated count and $T_n=\sum_{k=0}^{n-1}T_{n,k}$ the total count (trees included). Let $a_1\approx-2.338$ be the largest zero of the Airy function $\operatorname{Ai}$, and put

$$
D_n=(3n)^{-2/3}e^{a_1(3n)^{1/3}}\left(\frac{12}{e^2}\right)^n n^{2n},\qquad A=\frac{a_1^2}{6},\qquad \beta=-a_1,\qquad K=\pi\operatorname{Ai}'(a_1).
$$

**Theorem (maximal reticulation).** The amplitude $K=\pi\operatorname{Ai}'(a_1)$ is positive and

$$
\log\frac{M_n}{D_n}=\log\bigl(\pi\operatorname{Ai}'(a_1)\bigr)+\frac{a_1^2}{6}(3n)^{-1/3}-a_1(3n)^{-2/3}+\frac{13}{6}(3n)^{-1}+O(n^{-4/3}).
$$

This sharpens the order-of-magnitude estimate $M_n=\Theta(D_n)$ to an exact constant with three logarithmic corrections.

**Theorem (total count).** As $n\to\infty$,

$$
\frac{T_n}{M_n}=\sqrt e\,\exp\left(-\frac{\beta}{24}(3n)^{-2/3}+\frac{1}{288n}+O(n^{-4/3})\right),
$$

so that, with $K_{\mathrm{tot}}=\sqrt e\,\pi\operatorname{Ai}'(a_1)$,

$$
T_n=K_{\mathrm{tot}}\,D_n\exp\left(A(3n)^{-1/3}+\frac{23\beta}{24}(3n)^{-2/3}+\frac{209}{96}(3n)^{-1}+O(n^{-4/3})\right).
$$

**Defect generating function.** With the reticulation defect $d=n-1-k$ and $\mathcal G_n(z)=\sum_{d=0}^{n-1}\frac{T_{n,n-1-d}}{M_n}z^d$, for every fixed $R>0$, uniformly on $|z|\le R$,

$$
\mathcal G_n(z)=e^{z/2}\left(1-\frac{\beta z^2}{24}(3n)^{-2/3}+\frac{z^3}{96}(3n)^{-1}+O_R(n^{-4/3})\right).
$$

Thus a uniformly random tree-child network has a Poisson$(1/2)$-distributed reticulation defect in the limit, and summing over reticulations introduces no new amplitude constant beyond $\sqrt e$. Exactly, $T_{n,n-2}=M_n/2$ for $n\ge2$.

## Depends on

- [Brownian-excursion scaling function for tree-child networks](brownian-excursion-scaling-function-for-tree-child-networks.md)

## Expansion

Setting $n=m+1$ and $k=m$ in the exact coefficient formula $R_{n,k}=\sum_j f_jH_j(n,k)$ expresses $M_n$ through the whole coefficient sequence $f_j$, that is through the scaling function $F$. The coefficient sum becomes a contour integral whose saddle point is cubic; the spectral formula $F(z)=2\sqrt\pi\,z e^{-z^2/3}\sum_\nu e^{a_\nu z^{2/3}}$ shows that only the largest Airy zero $a_1$ survives, and the nominal leading term of the cubic saddle vanishes at $a_1$, which is why the derivative $\operatorname{Ai}'(a_1)$ appears in the amplitude. For the total, the ratios $T_{m+1,m-d}/M_{m+1}$ satisfy an exact recurrence in the defect $d$ and are approximated by $1/(2^dd!)$ with a summable error $O(2^dm^{-4/3}/(d+1)!)$; summing over $d$ gives $\sqrt e$ and the stated corrections.

## Sources

- Miquel Pons Viver, "Counting tree-child and reticulation visible networks", arXiv (2026), Section 3 (Theorem 3.1, Lemma 3.2) and Section 4 (Theorem 4.1, Lemmas 4.2–4.3, Proposition 4.4), <https://doi.org/10.48550/arXiv.2611.32460>
