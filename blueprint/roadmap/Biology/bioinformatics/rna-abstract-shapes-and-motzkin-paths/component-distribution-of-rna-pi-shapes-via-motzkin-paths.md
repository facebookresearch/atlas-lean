# Component distribution of RNA π-shapes via Motzkin paths

**Abstractions.** An RNA secondary structure is a noncrossing set of base pairs on a backbone. Its *π-shape* keeps only the branching pattern: every stem (including stems interrupted by bulges or interior loops) becomes a single bracket pair and all unpaired regions are deleted, so π-shapes are exactly the balanced bracket words with no directly nested pair $[[\cdots]]$. Its *island diagram* removes the tails and replaces each maximal run of unpaired bases between helices by a single blank.

**Proposition (island diagrams).** Let $g(h,I,\ell)$ count island diagrams with $h$ hairpins, $I$ islands and $\ell$ base pairs, and let $N(\ell,h)=\frac1\ell\binom{\ell}{h}\binom{\ell}{h-1}$ be the Narayana numbers. Then

$$G(x,y,z)=\sum_{\ell,h}N(\ell,h)\,x^hy^{h+1}(1+y)^{2\ell-1-h}z^\ell=\frac{y}{1+y}\cdot\frac{1-A(1+B)-\sqrt{1-2A(1+B)+A^2(1-B)^2}}{2A},$$

with $A=z(1+y)^2$ and $B=xy/(1+y)$. Comparing with a 2-Motzkin path expansion gives, for $\ell\ge1$, an identity between Narayana numbers and Motzkin polynomial coefficients $M(n,p)$ (paths of length $n$ with $p$ up steps):

$$\frac{y}{1+y}\sum_{h=1}^{\ell}N(\ell,h)(xy)^h(1+y)^{2\ell-h}=xy^2\sum_{p=0}^{\lfloor(\ell-1)/2\rfloor}M(\ell-1,p)\big(xy(1+y)^3\big)^p\big((1+y)(1+y+xy)\big)^{\ell-2p-1}.$$

**Bijection.** π-shapes of length $2n+2$ correspond bijectively to Motzkin paths of length $n$: up steps correspond to multiloops, the number of hairpins is $u+r+1$ ($u$ up steps, $r$ horizontal steps), and a π-shape with $r_0+1$ components (branches of the exterior loop) corresponds to a path with $r_0$ horizontal steps at level 0.

**Theorem (components of π-shapes).** Let $M(r_0;n)$ be the number of Motzkin paths of length $n$ with $r_0$ level-0 horizontal steps and $M_n$ the Motzkin number. For fixed $r_0$,

$$\lim_{n\to\infty}\frac{M(r_0;n)}{M_n}=\frac{r_0+1}{2^{r_0+2}},\qquad \lim_{n\to\infty}\frac{\sum_{r_0}r_0M(r_0;n)}{M_n}=2 .$$

So the number of components of a uniformly random π-shape is asymptotically a negative binomial law with mean $3$.

**Theorem (π-shapes compatible with structures of length $\nu$).** Fix a minimum arc length $\lambda\ge1$ (every hairpin loop has at least $\lambda-1$ unpaired bases), and let $\pi_\lambda(r_0;\nu)$ count π-shapes with $r_0+1$ components to which secondary structures of length $\nu$ reduce. Let $\zeta_\lambda$ be the smallest positive real root of $z^{2\lambda+2}-4z^{\lambda+3}-2z^{\lambda+1}+1$. Then for fixed $r_0$,

$$\lim_{\nu\to\infty}\frac{\pi_\lambda(r_0;\nu)}{\pi_\lambda(\nu)}=(r_0+1)\,\frac{\zeta_\lambda^2}{1+\zeta_\lambda^2}\Big(\frac{1+\zeta_\lambda^{\lambda+1}}{2(1+\zeta_\lambda^2)}\Big)^{r_0},\qquad \lim_{\nu\to\infty}\frac{\sum_{r_0}r_0\,\pi_\lambda(r_0;\nu)}{\pi_\lambda(\nu)}=\frac{1-\zeta_\lambda^{\lambda+1}}{\zeta_\lambda^2}.$$

## Expansion

Decomposing a Motzkin path at its level-0 horizontal steps writes it as $r_0+1$ (possibly empty) blocks of elevated excursions separated by $r_0$ horizontal steps, so the generating function marking $r_0$ is $E(z)/(1-tzE(z))$, where $E(z)=1/(1-z^2m(z))$ counts sequences of elevated excursions and the Motzkin series $m(z)$ has a square-root singularity at $z=1/3$. By the Flajolet–Odlyzko transfer theorem the coefficient ratio converges to the law $(r_0+1)q^{r_0}(1-q)^2$ with $q=zE(z)$ evaluated at the singularity; here $q=1/2$, which gives $(r_0+1)/2^{r_0+2}$. For compatible shapes the same argument applies to the substituted series $\frac{z^{\lambda+1}}{1-z}m(t;z^{1-\lambda},z^{\lambda+1})$, whose dominant singularity is the root $\zeta_\lambda$.

## Sources

- Sang Kwan Choi, "Motzkin path on RNA abstract shapes", arXiv:1907.07334 (2019): Proposition 2.1, Theorem 2.1, Section 3.1 and Table 1 (bijection), Proposition 3.1, Theorems 3.1 and 3.2, Appendix 6. <https://doi.org/10.48550/arXiv.1907.07334>
