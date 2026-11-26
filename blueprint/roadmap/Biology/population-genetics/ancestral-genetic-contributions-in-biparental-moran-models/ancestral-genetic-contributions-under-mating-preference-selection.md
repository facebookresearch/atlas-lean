# Ancestral genetic contributions under mating-preference selection

**Setting.** A population of $N$ haploid hermaphrodites evolves by a biparental Moran model. Each individual carries allele $0$ or $1$ at a selected biallelic locus. At each step a mother is chosen uniformly; she chooses a father, a given type-1 individual being $1+s_i$ times more likely to be chosen than a given type-0 individual when the mother has type $i$; one parent, chosen with probability $1/2$, transmits its allele to a single offspring, which replaces a uniformly chosen individual. Two patterns are considered: **increased attractiveness** ($s_0=s_1=s>0$) and **homogamous choosiness** ($s_0=0$, $s_1=s>0$). At an unlinked neutral locus, the *genetic weight* $W_n(l,l')$ is the probability, given the pedigree, that a gene sampled in individual $l$ at time $n$ descends from ancestor $l'$ at time $0$. With $\mathcal Y_n$ the set of type-1 individuals at time $n$ and $Y_n=|\mathcal Y_n|$, let
$$U_n=\sum_{l\in\mathcal Y_n}\sum_{l'\in\mathcal Y_0}W_n(l,l'),\qquad V_n=\sum_{l\notin\mathcal Y_n}\sum_{l'\in\mathcal Y_0}W_n(l,l'),$$
the amount of genome carried by advantaged (respectively disadvantaged) individuals that comes from the initially advantaged ancestors, and $Z_n=(Y_n,U_n,V_n)/N$.

**Theorem 3.1 (deterministic limit, increased attractiveness).** If $Y_0/N\to b\in(0,1)$ in probability, then for every $c>0$, $\sup_{0\le t\le c}\|Z_{\lfloor Nt\rfloor}-z_a(t)\|\to0$ in probability, where $z_a=(y,u,v)$ is the unique solution with $z_a(0)=(b,b,0)$ of
$$y'=\frac{(s/2)\,y(1-y)}{1+sy},\quad u'=-\frac{u(1-y)}{1+sy}+\frac{2+s}{4}\,\frac{vy+(1-y)u}{1+sy},\quad v'=-\frac{(1+s)\,vy}{1+sy}+\frac{2+s}{4}\,\frac{vy+(1-y)u}{1+sy}.$$
Theorem 3.3 gives the analogous limit $z_h$ for homogamous choosiness.

**Proposition 3.7 and Proposition 3.8 (comparison).** For the same $s$ and $b$, for all $t>0$: $y_h(t)<y_a(t)$ and $u_h(t)+v_h(t)<u_a(t)+v_a(t)$; that is, homogamous choosiness spreads the advantaged allele more slowly and leaves initially advantaged ancestors a smaller total genetic contribution. For finite $s$, $u_h(\infty)<u_a(\infty)<u_d(\infty)$, where $u_d$ refers to viability selection of the same strength.

**Corollary 3.9 (infinite selection).** When $s=\infty$, both mating patterns give the same limiting contribution of initially advantaged ancestors:
$$\lim_{t\to\infty}u_a(t)=\lim_{t\to\infty}u_h(t)=\sqrt{\frac{b}{1-b}}\,\arctan\sqrt{\frac{1-b}{b}}.$$

## Expansion

Each Moran step changes $Z_n$ by $O(1/N)$ with conditional drift $N^{-1}g(Z_n)$, so after the time change $n=\lfloor Nt\rfloor$ a standard martingale argument shows $Z$ follows the ODE $z'=g(z)$. The $y$-equation is a logistic-type equation solved by $y_a(t)=\sigma^{-1}(\sigma(b)e^{st/2})$ for an explicit increasing $\sigma$ (Proposition 3.2). For $u$ and $v$, neutral genome from initially advantaged ancestors is lost from a class when one of its members is replaced and gained when a newborn inherits from a parent carrying such genome; the $u$ and $v$ equations are linear given $y$, so they are solved by integrating along $y_a$ (Proposition 3.2). As $s\to\infty$ only the timing of the sweep matters, which is why the two mating patterns give the same limit in Corollary 3.9.

## Sources

- J. Mardomingo-Sanz, R. Tran-Thanh, C. Coron, D. Abu Awad, "How timing and mode of selection shape ancestral genetic contributions", arXiv preprint (2026), Theorem 3.1, Proposition 3.2, Theorem 3.3, Propositions 3.7 and 3.8, Corollary 3.9, <https://doi.org/10.48550/arXiv.2611.00161>.
