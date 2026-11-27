# Partition moments close in the Moran recombination model

**Model.** Let $S = \{1, \dots, n\}$ be a set of sites with finite allele sets $X_i$ and type space $X = X_1 \times \dots \times X_n$. For $G \subseteq S$ and types $x, y$ let $p_G(x,y)$ be the type carrying the alleles of $x$ at the sites in $G$ and those of $y$ at the sites in $\bar G = S \setminus G$. A population of $N$ individuals evolves as a continuous-time Markov chain $Z_t$ on counting measures on $X$ (with $Z_t(X) = N$):

- *recombination:* for every $G \subseteq S$ and types $x, y$, the pair $x, y$ is replaced by $p_G(x,y), p_{\bar G}(x,y)$ at rate $\frac1N \varrho_G\, Z_t(x) Z_t(y)$, where $\varrho_G = \varrho_{\bar G} \ge 0$ and $\varrho_\varnothing = \varrho_S = 0$;
- *mutation:* allele $x_i$ at site $i$ becomes $y_i$ at rate $\mu^i_{x_i y_i}$ per individual;
- *resampling:* at rate $\frac{b}{2N} Z_t(x)Z_t(y)$ an individual of type $y$ is replaced by a copy of type $x$.

Fix a reference type $x$ and, for $A \subseteq S$, let $[A]_t$ be the number of individuals that agree with $x$ at all sites of $A$ (the marginal count, with $[\varnothing]_t = N$). For every $I \subseteq S$ the marginal process $\pi_I . Z_t$ is again a Markov chain, a recombination process on the sites $I$ with rates $\varrho^{(I)}_H = \sum_{G:\, G \cap I = H} \varrho_G$.

**Theorem.**

1. *(Recombination alone, $\mu = b = 0$.)* For every partition $\mathcal A = \{A_1, \dots, A_m\}$ of $S$, $\frac{d}{dt}\mathbb E\big[\prod_{\ell=1}^m [A_\ell]_t\big]$ is a finite linear combination, with coefficients built from the $\varrho_G/(4N)$, of expectations $\mathbb E\big[\prod_{B \in \mathcal B}[B]_t\big]$ over partitions $\mathcal B$ of $S$ (obtained from $\mathcal A$ by cutting and regrouping blocks along recombination sets $G$). In particular, for the full type,

$$ \frac{d}{dt}\mathbb E\big[[S]_t\big] = \sum_{G \subseteq S} \frac{\varrho_G}{2N}\Big(\mathbb E\big[[G]_t\,[\bar G]_t\big] - N\, \mathbb E\big[[S]_t\big]\Big). $$

   Hence the expectations of all partition products form a closed hierarchy, described exhaustively by a finite system of linear ODEs: the moment approach closes.
2. *(Recombination and mutation.)* Adding mutation adds only terms linear in partition products (single-site changes replace $[A_\ell]_t$ by $[A_\ell \setminus \{j\}]_t$ or by itself), so the moment system still closes.
3. *(Recombination and resampling, two sites, $\mu = 0$, $b > 0$, $S = \{1,2\}$.)* Resampling makes the one-site marginals random, yet the two moments $\mathbb E\big[[1,2]_t\big]$ and $\mathbb E\big[[1]_t[2]_t\big]$ still form a finite closed linear system:

$$\frac{d}{dt}\mathbb E\big[[1,2]_t\big] = \frac{\varrho_{\{1\}}}{N}\,\mathbb E\big[[1]_t[2]_t - N[1,2]_t\big], \qquad \frac{d}{dt}\mathbb E\big[[1]_t[2]_t\big] = \frac{b}{N}\,\mathbb E\big[N[1,2]_t - [1]_t[2]_t\big],$$

   so the expected linkage disequilibrium $\mathbb E\big[N[1,2]_t - [1]_t[2]_t\big]$ decays exponentially at rate $\varrho_{\{1\}} + b/N$. (Note: equation (22) of arXiv:1105.0793 prints $(\varrho_1 + b)/N$, whereas equations (20)–(21) give $\varrho_{\{1\}} + b/N$.)

For three or more sites with resampling the source argues only heuristically that closure fails, and this page claims nothing there.

## Expansion

For a finite-state Markov chain, $\frac{d}{dt}\mathbb E[Z_t] = \mathbb E[F(Z_t)]$ with $F(z) = \sum_v v\, q(z, z+v)$. The count of the full type changes through recombination events that create it from individuals matching it on complementary site sets $G$ and $\bar G$ (rate proportional to $[G]_t[\bar G]_t$) or break it up (rate proportional to $N[S]_t$), giving the displayed equation, whose right side involves a product indexed by the partition $\{G, \bar G\}$. Iterating, a recombination event with set $G$ acting on a product $\prod_\ell [A_\ell]_t$ only splits and regroups blocks, and no site ever appears in two factors, so every new term is again a partition product; since $S$ has finitely many partitions the hierarchy is finite. In the single-crossover case the induced marginals are moreover conditionally independent, which reduces the system to the deterministic recombination equation, but with general recombination products of non-ordered partitions appear and independence is lost, so closure is the exceptional structural fact. With resampling and two sites, recombination leaves the one-site counts unchanged, and the resampling drift of $[1]_t[2]_t$ is again a combination of $N[1,2]_t$ and $[1]_t[2]_t$, which gives the two-site system of item 3.

## Sources

- Ellen Baake, Thiemo Hustedt, "Moment closure in a Moran model with recombination", *Markov Processes and Related Fields* 17 (2011), 429–446; preprint arXiv:1105.0793, <https://doi.org/10.48550/arXiv.1105.0793>. Numbering of the arXiv version: Section 2 (model, Proposition 1), Section 3.1 (Lemma 1, mean equation for the full type, Definition 1, Theorem 1, Corollary 1), Section 4 (mutation), Section 5 (resampling, equations (20)–(22)).
