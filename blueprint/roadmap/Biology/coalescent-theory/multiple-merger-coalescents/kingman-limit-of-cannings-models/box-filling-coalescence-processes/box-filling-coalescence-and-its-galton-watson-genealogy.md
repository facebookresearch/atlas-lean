# Box-filling coalescence process and its Bienaymé–Galton–Watson genealogy

**Construction.** Start at step $0$ with infinitely many boxes of size $K^*_0(i)=1$, $i\ge1$. At step $n+1$, consecutive boxes are merged in groups of random sizes $M_{n+1}(1),M_{n+1}(2),\dots$ (i.i.d. with probability generating function $f_{n+1}$, the *coalescing mechanism* at step $n+1$; a group of size $0$ produces an empty box):

$$K^*_{n+1}(i)=\sum_{m=1}^{M_{n+1}(i)}K^*_n\Bigl(m+\sum_{j=1}^{i-1}M_{n+1}(j)\Bigr),\qquad K^*_{n+1}(i)=0\ \text{if }M_{n+1}(i)=0 .$$

**Proposition.** For each $n$ the box sizes $\{K^*_n(i)\}_{i\ge1}$ are i.i.d., with $K^*_{n+1}\overset{d}{=}\sum_{m=1}^{M_{n+1}}K^{*(m)}_n$, hence

$$\mathbb E\,z^{K^*_n}=\phi^*_n(z)=f_n\bigl(f_{n-1}(\cdots f_1(z))\bigr),\qquad \mathbb P(K^*_N=0)=\phi^*_N(0),\qquad \mathbb E K^*_N=\prod_{n=1}^Nf_n'(1).$$

The process is called subcritical, critical or supercritical according as $\mu=\lim_N(\mathbb EK^*_N)^{1/N}$ is $<1$, $=1$ or $>1$.

**Theorem (genealogy).** Fix a terminal step $N$ and a box of size $j$ (an event of probability $\mathbb P(K^*_N=j)$). Its ancestral tree, read backward from step $N$ to step $0$, is a time-inhomogeneous Bienaymé–Galton–Watson tree started from one individual with offspring pgfs $g_1=f_N,g_2=f_{N-1},\dots,g_N=f_1$ (so $\mathbb E z^{K_\nu}=f_N(f_{N-1}(\cdots f_{N-\nu+1}(z)))$), conditioned to have $j$ individuals at generation $N$.

**Exactly solvable mechanisms.** The family $f_n(z)=z_c-\bigl(a_n(z_c-z)^{-\theta}+b_n\bigr)^{-1/\theta}$ (generalized linear-fractional, with $\theta=1$ the linear-fractional case) is closed under composition:

$$\phi^*_n(z)=z_c-\bigl(A^*_n(z_c-z)^{-\theta}+B^*_n\bigr)^{-1/\theta},\qquad A^*_n=\prod_{m=1}^na_m,\quad B^*_n=\sum_{k=1}^nb_k\prod_{l=k+1}^na_l ,$$

so the empty-box probability $\mathbb P(K^*_N=0)=z_c-(A^*_Nz_c^{-\theta}+B^*_N)^{-1/\theta}$ and the mean box size have closed forms. A quadratic mechanism obtained by normalizing iterates $f^{\circ n}(z)/f^{\circ n}(1)$ of a quadratic map gives a second explicit time-inhomogeneous example.

## Depends on

- [Generation-size law of a Galton–Watson process](../../../../../Probability/branching-processes/galton-watson-process/law.md)

## Proof depends on

- [Generating function of the n-th generation size](../../../../../Probability/branching-processes/galton-watson-process/pgf-law.md)

## Expansion

Disjoint consecutive groups are formed from disjoint blocks of i.i.d. boxes, so the new box sizes are again i.i.d. and each is a random sum, which composes generating functions in the order $f_n\circ\dots\circ f_1$. Reading the merging history of one final box backward, each box at step $n$ splits into $M_n$ boxes at step $n-1$, independently, which is a branching process with offspring laws $f_N,\dots,f_1$; requiring the final box to have size $j$ is conditioning that tree to have $j$ leaves. Composition-closed families are those conjugate to affine maps, here $z\mapsto(z_c-z)^{-\theta}$, which turns iteration into products and sums of the coefficients.

## Sources

- Nicolas Grosjean and Thierry Huillet, *On a coalescence process and its branching genealogy*, J. Appl. Probab. 53(4) (2016), 1156–1165. <https://doi.org/10.1017/jpr.2016.71> Definitions 1–3, Proposition 1, Theorem 2 and the propositions on the generalized linear-fractional and quadratic coalescing mechanisms. Locators use the numbering of the preprint arXiv:1709.07633.
