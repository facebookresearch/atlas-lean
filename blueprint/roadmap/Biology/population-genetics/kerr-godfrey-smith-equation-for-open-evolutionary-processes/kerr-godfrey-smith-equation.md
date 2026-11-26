# Kerr–Godfrey-Smith equation for open evolutionary processes

**Setting.** A parent population is a finite measure $\mu$ on $(I,\mathcal I)$ of size $N>0$ and a child population is a finite measure $\mu'$ on $(I',\mathcal I')$ of size $N'>0$. In an *open* process not every child has an accounted parent: $\mu'=\mu'_\pi+\mu'_\nu$ splits into a parented deme $\mu'_\pi$ of size $N'_\pi>0$ and an orphaned deme $\mu'_\nu$ (immigrants, children of unobserved parents), and only the parented deme is produced by a (closed) evolutionary process $w_\pi:\mu\mapsto\mu'_\pi$, i.e. $\mu'_\pi(B)=\int_I w_{\pi,i}(B)\,\mu(\mathrm di)$.

Write $p'_\pi=N'_\pi/N'$, $W_\pi(i)=w_{\pi,i}(I')$, $\bar W_\pi=N'_\pi/N$, relative fitness $U=W_\pi/\bar W_\pi$, local average $\langle Y\rangle(i)=W_\pi(i)^{-1}\int Y\,\mathrm dw_{\pi,i}$, and let $\pi=\mathrm d\mu'_\pi/\mathrm d\mu'$ and $\nu=\mathrm d\mu'_\nu/\mathrm d\mu'=1-\pi$ be the deme densities. Let $\mathbb E,\operatorname{Cov}$ be averages under $\mu/N$ and $\mathbb E',\operatorname{Cov}'$ averages under $\mu'/N'$.

**Open tower property.** For every integrable observable $Y$ on $I'$,

$$\mathbb E'[Y]=\mathbb E\bigl[\langle Y\rangle\,U\bigr]+\frac1{p'_\pi}\operatorname{Cov}'(Y,\nu)=\mathbb E\bigl[\langle Y\rangle\,U\bigr]-\frac1{p'_\pi}\operatorname{Cov}'(Y,\pi).$$

**Statement.** If $U$ has finite variance, then for all observables $X$ on $I$ and $Y$ on $I'$,

$$\mathbb E'[Y]-\mathbb E[X]=\operatorname{Cov}(X,U)+\mathbb E\bigl[(\langle Y\rangle-X)\,U\bigr]+\frac1{p'_\pi}\operatorname{Cov}'(Y,\nu).$$

The first two terms are the selection and transmission terms of the Price equation for the parented children; the third is the shift caused by orphans, positive when orphans carry above-average $Y$. When $\mu'_\nu=0$ it vanishes and the Price equation is recovered.

## Depends on

- [Price equation](../natural-selection-fisher-s-theorem-and-the-price/price.md)

## Expansion

The densities exist because each deme is dominated by $\mu'$. Then $\mathbb E'[Y\pi]=p'_\pi\,\mathbb E'_\pi[Y]$ and, by disintegration of $\mu'_\pi$, $\mathbb E'_\pi[Y]=\mathbb E[\langle Y\rangle U]$. Writing $\mathbb E'[Y]=\mathbb E'[Y\pi]+\mathbb E'[Y\nu]$ and $\mathbb E'[Y\nu]=\operatorname{Cov}'(Y,\nu)+(1-p'_\pi)\mathbb E'[Y]$, then solving for $\mathbb E'[Y]$, gives the open tower property. The equation follows from $\mathbb E'[Y]-\mathbb E[X]=(\mathbb E[XU]-\mathbb E[X])+(\mathbb E'[Y]-\mathbb E[XU])$ with $\mathbb E[XU]-\mathbb E[X]=\operatorname{Cov}(X,U)$. The source prints the middle term as $\mathbb E[\langle Y\rangle U]$; the form above, with the local change $\langle Y\rangle-X$, is what its one-line proof yields and is the version consistent with the closed Price equation. In the discrete edge-counting case this reduces to the original equation of Kerr and Godfrey-Smith, with the orphan term written through the number of accounted parents of each child (the dual fitness).

## Sources

- T. LaGatta, *The Mathematics of Evolution: The Price Equation, Natural Selection, and Environmental Change*, arXiv:2202.10289 (2022): Section 10, Lemma 10.2 (open tower property), Theorem 10.3 (Kerr–Godfrey-Smith equation), Corollary 10.4 (dual-fitness version). <https://doi.org/10.48550/arXiv.2202.10289>
- B. Kerr and P. Godfrey-Smith, Generalization of the Price equation for evolutionary change, Evolution 63 (2009), 531–536.
