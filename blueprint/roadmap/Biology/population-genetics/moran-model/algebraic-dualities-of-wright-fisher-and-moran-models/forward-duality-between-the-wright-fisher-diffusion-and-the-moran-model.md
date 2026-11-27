# Forward duality between the multitype Wright–Fisher diffusion and the Moran model

**Models.** Fix $d \ge 2$ types and a symmetric parent-independent mutation rate $\theta \ge 0$. The **$d$-type Wright–Fisher diffusion** on the simplex $\{x \in [0,1]^{d} : \sum_i x_i = 1\}$ has generator, in the coordinates $x_1, \dots, x_{d-1}$,

$$\mathscr L^{WF}_{d,\theta}\,g(x) = \sum_{i=1}^{d-1}\frac12 x_i(1-x_i)\,\partial_{x_i}^2 g - \sum_{1 \le i < j \le d-1} x_i x_j\,\partial_{x_i}\partial_{x_j} g + \frac{\theta}{d-1}\sum_{i=1}^{d-1}(1 - d x_i)\,\partial_{x_i} g.$$

The **$d$-type Moran model** with $N$ individuals has type counts $k = (k_1, \dots, k_d)$, $\sum_i k_i = N$; for every ordered pair of distinct types $i \ne j$, at rate $\frac12 k_i\big(k_j + \frac{2\theta}{d-1}\big)$ one individual of type $i$ becomes of type $j$ (resampling plus mutation). Two Markov processes $X$ and $K$ are **dual** with duality function $D$ if $\mathbb E_x\big[D(X_t, k)\big] = \mathbb E_k\big[D(x, K_t)\big]$ for all $t \ge 0$ and all initial states.

**Theorem 1 (Wright–Fisher–Moran duality).** For $\theta > 0$, the $d$-type Wright–Fisher diffusion and the $d$-type Moran model with $N$ individuals are dual with duality function

$$\tilde D_N(x, k) = \prod_{i=1}^{d}\frac{x_i^{k_i}}{\Gamma\big(\frac{2\theta}{d-1} + k_i\big)}.$$

**Theorem 2 (self-duality of the Moran model).** For $\theta > 0$, the $d$-type Moran model with $N$ individuals is self-dual with duality function

$$\bar D_N(k, \xi) = \prod_{i=1}^{d}\frac{k_i!}{(k_i - \xi_i)!}\,\frac{\Gamma\big(\frac{2\theta}{d-1}\big)}{\Gamma\big(\xi_i + \frac{2\theta}{d-1}\big)}, \qquad \sum_i \xi_i = N,$$

with a limiting self-duality as $\theta \to 0$.

Unlike the classical moment duality between the Wright–Fisher diffusion and the block-counting process of Kingman's coalescent (which runs backward in time), both processes here are forward evolutions of a population.

## Expansion

The method writes generators in terms of operators satisfying a Lie algebra's commutation relations and obtains dualities from changes of representation. Classical forward/ancestral dualities correspond to the Heisenberg algebra of creation and annihilation operators $a^\dagger = x$, $a = \partial_x$ and their discrete counterparts. The new dualities use the $SU(1,1)$ algebra: the operators $K^+_i = x_i$, $K^-_i = x_i\partial_{x_i}^2 + \frac m2\partial_{x_i}$, $K^0_i = x_i\partial_{x_i} + \frac m4$ represent $SU(1,1)$ on functions of $x$, and the dual discrete representation acts on occupation numbers. The Brownian energy process $\mathrm{BEP}(m)$ and the symmetric inclusion process $\mathrm{SIP}(m)$ on the complete graph with $d$ vertices are built from these operators and are dual; conditioning on the conserved total (mass $1$ for BEP, $N$ particles for SIP) turns them into the Wright–Fisher diffusion and the Moran model with $\frac{m}{2} = \frac{2\theta}{d-1}$, and the self-duality of SIP gives Theorem 2.

## Sources

- Gioia Carinci, Cristian Giardinà, Claudio Giberti, Frank Redig, "Dualities in population genetics: a fresh look with new dualities", *Stochastic Processes and their Applications* 125 (2015), 941–969, <https://doi.org/10.1016/j.spa.2014.10.009>; preprint arXiv:1302.3206, <https://doi.org/10.48550/arXiv.1302.3206>. Numbering of the arXiv version: Section 3 (Heisenberg algebra), Section 4 (classical dualities), Section 5 (Propositions on BEP/SIP and Wright–Fisher/Moran correspondence, Theorems 5.1 and 5.2).
