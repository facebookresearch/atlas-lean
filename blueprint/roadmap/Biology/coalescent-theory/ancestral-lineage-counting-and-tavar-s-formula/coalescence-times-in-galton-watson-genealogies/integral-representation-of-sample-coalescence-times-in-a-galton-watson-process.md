# Integral representation of sample coalescence times in a Galton–Watson process

**Setting.** Let $(N_t(n_0))_{t\ge0}$ be a Bienaymé–Galton–Watson process started from $n_0$ founders, with offspring probability generating function $\phi$ and $t$-fold iterate $\phi_t=\phi\circ\dots\circ\phi$, so $\mathbb E\,u^{N_t(n_0)}=\phi_t(u)^{n_0}$; $f^{(i)}$ denotes the $i$-th derivative. Sample $i$ individuals without replacement from generation $t$ (on $\{N_t(n_0)\ge i\}$), let $\widehat N_s$ be the number of distinct ancestors of the sample in generation $s\le t$ (so $\widehat N_t=i$), and let

$$\tau^{(t)}_{i,1}(n_0)=\sup\{0\le s<t:\widehat N_s=1\}$$

be the generation of their most recent common ancestor, counted forward from the founders at generation $0$, with $\tau=\infty$ if this set is empty (the sample descends from different founders, or $N_t(n_0)<i$). Thus $\tau\ge k$ means that the sample coalesces within the last $t-k$ generations.

**Lemma (size-biased sampling identity).** For i.i.d. nonnegative integer variables $M_1,\dots,M_n$ with pgf $\phi$ and falling factorials $(m)_i$,

$$\mathbb E\!\left[\frac{(M_1)_i}{\big(\sum_{l=1}^nM_l\big)_i}\right]=\frac1{\Gamma(i)}\int_0^1(1-z)^{i-1}\phi(z)^{n-1}\phi^{(i)}(z)\,dz ,$$

and more generally, for $i_1+\dots+i_j=i$, $\mathbb E\big[\prod_{l=1}^j(M_l)_{i_l}\big/\big(\sum_{l=1}^nM_l\big)_i\big]=\frac1{\Gamma(i)}\int_0^1(1-z)^{i-1}\phi(z)^{n-j}\prod_{l=1}^j\phi^{(i_l)}(z)\,dz$. The denominator is the single falling factorial $(\sum M)_i$, the probability weight of drawing an ordered $i$-sample; the source's displays (Eq. (1) and Corollary 10) print one factor $(\sum M)_{i_l}$ per $l$, which is a misprint, since for $j=1$ they must reduce to the identity above.

**Theorem (TMRCA of a sample).** For $0\le k\le t-1$,

$$\mathbb P\big(\infty>\tau^{(t)}_{i,1}(n_0)\ge k\big)=\frac1{\Gamma(i)}\int_0^1(1-z)^{i-1}\big[\phi_t^{n_0}\big]^{(1)}(z)\,\frac{\phi_{t-k}^{(i)}(z)}{\phi_{t-k}^{(1)}(z)}\,dz ,$$

and $\mathbb P(\tau^{(t)}_{i,1}(n_0)<\infty)$ is the case $k=0$. For two individuals, the probability that they descend from different founders is $n_0(n_0-1)\int_0^1(1-z)\,\phi_t^{(1)}(z)^2\phi_t(z)^{n_0-2}\,dz$.

**Theorem (whole-population TMRCA).** For a single founder, conditionally on survival to generation $t$,

$$\mathbb P\big(\tau^{(t)}_{N_t(1),1}(1)\ge k\mid N_t(1)>0\big)=\frac{\mathbb P(N_{t-k}(1)>0)}{\mathbb P(N_t(1)>0)}\;\phi_k^{(1)}\big(\mathbb P(N_{t-k}(1)=0)\big).$$

The first backward step of the ancestral count has explicit probabilities of the same integral form: on $\{N_t(n_0)\ge i\}$, $\mathbb P(\widehat N_{t-1}=j)=\frac1{j!\,\Gamma(i)}\sum^*_{i_1+\dots+i_j=i}\binom{i}{i_1,\dots,i_j}\int_0^1(1-z)^{i-1}\big[\phi_{t-1}^{n_0}\big]^{(j)}(\phi(z))\prod_{l=1}^j\phi^{(i_l)}(z)\,dz$, with all $i_l\ge1$, and these sum over $j$ to $\mathbb P(N_t(n_0)\ge i)$. The process $s\mapsto\widehat N_s$ is not a Markov chain with the one-step transition matrices of Proposition 1, so its multi-generation laws, such as the TMRCA law above, do not factor into products of one-step matrices. The source says otherwise ("The count genealogy process is a time-inhomogeneous integral-valued Markov process", Section 2.1, just before Proposition 1). The page differs because, given $\widehat N_{t-1}=j$, the law of $\widehat N_{t-2}$ still depends on $\widehat N_t$, which carries information about the generation size $N_{t-1}$. Exact enumeration for offspring uniform on $\{0,1,2,3\}$, $n_0=2$, $t=2$ gives $\mathbb P(\widehat N_0=1\mid\widehat N_1=2)\approx0.5270$ when two individuals are sampled ($\widehat N_2=2$) and $\approx0.5553$ when three are sampled ($\widehat N_2=3$).

## Depends on

- [Generating function of the n-th generation size](../../../../Probability/branching-processes/galton-watson-process/pgf-law.md)
- [Labelled Galton–Watson trees and projection to generation counts](../../../../Probability/branching-processes/galton-watson-process/ulam-harris-labelled-galton-watson-trees-and-pro.md)

## Expansion

Conditionally on generation $t-1$, the offspring numbers of the $N_{t-1}$ parents are i.i.d. with pgf $\phi$, and sampling $i$ children without replacement picks children of one given parent with probability $(M_1)_i/(\sum M)_i$; the identity follows by writing $(M_1)_i/(\sum M)_i$ via the Beta integral $\frac{\Gamma(a)\Gamma(b)}{\Gamma(a+b)}=\int_0^1z^{a-1}(1-z)^{b-1}dz$ and exchanging expectation and integral, which turns ratios of falling factorials into derivatives of the pgf. Iterating over generations and using the branching property ($\phi_{t}=\phi_k\circ\phi_{t-k}$) gives the TMRCA law. For the whole population, the most recent common ancestor of all survivors lives in generation $k$ or later iff exactly one individual at generation $k$ has surviving descendants at $t$, which produces $\phi_k^{(1)}$ evaluated at the extinction probability. Closed forms follow for $b$-ary, linear-fractional and Sibuya (infinite-mean) offspring laws, whose iterates are explicit.

## Sources

- Nicolas Grosjean and Thierry Huillet, "On the genealogy and coalescence times of Bienaymé–Galton–Watson branching processes", *Stoch. Models* 34(1) (2018), 1–24. <https://doi.org/10.1080/15326349.2017.1375958>
- Preprint version (the locators in this item follow its numbering): Nicolas Grosjean, Thierry Huillet, "On the genealogy and coalescence times of Bienaymé-Galton-Watson branching processes", arXiv:1709.07630: Proposition 1 and Corollary 2 (ancestral count transition matrix), Theorem 3 and Corollary 4 (coalescence and TMRCA laws), Proposition 5 and Corollaries 6–7 (finiteness and conditional laws), Theorem 8 (whole-population TMRCA), Lemma 9 and Corollary 10 (sampling identity), Section 4 (examples). <https://doi.org/10.48550/arXiv.1709.07630>
