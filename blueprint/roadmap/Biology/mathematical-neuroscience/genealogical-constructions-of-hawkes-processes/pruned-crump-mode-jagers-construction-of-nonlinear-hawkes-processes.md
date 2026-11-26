# Pruned Crump–Mode–Jagers construction of nonlinear Hawkes processes

**CMJ forest.** Individuals are indexed by a forest of Ulam–Harris words and have infinite lifetimes. Birth times $\theta(u)$ are of three kinds: the atoms of a given locally finite initial point process $N^-$ on $(-\infty,0]$; immigrants arriving as a Poisson process of rate $\mu \ge 0$ on $[0,\infty)$; and offspring, each individual $v$ giving birth at the times $\theta(v) + t^v_i$ of an independent inhomogeneous Poisson process with intensity $h \ge 0$ (a locally integrable reproduction kernel). Let $N = \sum_{\theta(u)<\infty}\delta_{\theta(u)}$ be the birth-time point process, and $A_tN$ the age structure at time $t$, $A_tN([a,b]) = N([t-b,t-a])$.

**Theorem (linear case).** Assume $\mathbb E\big[\int_0^T dt\int_{-\infty}^0 h(t-s)\,dN^-_s\big] < \infty$ for all $T$. Then $N$ is a simple, locally finite point process with $N|_{(-\infty,0]} = N^-$ and intensity

$$\lambda(t) = \mu + \int_{-\infty}^t h(t-s)\,dN_s,$$

i.e. $N$ is the linear Hawkes process with parameters $(N^-, \psi(x) = \mu + x, h)$. No subcriticality condition $\|h\|_1 < 1$ is needed.

**Pruning by hereditary types.** Give every individual a type $\chi(u) \in \{0,1\}$: the initial population has type $1$; an immigrant or child born at time $t$ of a type-$1$ parent (or immigrating) receives type $1$ with probability $\psi(Z^1_{t^-})$, where $\psi : \mathcal M(\mathbb R_+) \to [0,1]$ is measurable for the vague topology and $Z^1_{t^-}$ is the age structure of type-$1$ individuals born before $t$; type $0$ is absorbing and inherited. Let $N^1$ be the birth-time process of type-$1$ individuals.

**Theorem (nonlinear case).** Under the same assumptions on $h$ and $N^-$, $N^1$ is a simple, locally finite point process with intensity

$$\lambda^1(t) = \psi\big(A_tN^1\big)\Big(\mu + \int_{-\infty}^t h(t-s)\,dN^1_s\Big),$$

and every atom of $N^1$ is an atom of $N$, so $N^1 \le N$.

Choosing $\psi(A_tN^1) = \phi\big(\int f(t-s)\,dN^1_s\big)$ with $\phi : \mathbb R \to [0,1]$ gives the multiplicative-inhibition Hawkes model of interacting neuron populations; choosing $\psi$ to vanish during a window after each event gives refractory periods (infinite inhibition). The construction embeds a genealogy in nonlinear Hawkes processes and couples them below a linear Hawkes process.

## Expansion

In the linear case, the conditional intensity at $t$ given the past is the sum of the immigration rate and the reproduction intensities of all individuals already born, which is exactly the Hawkes intensity; this is the Poisson cluster representation, extended to arbitrary initial conditions and to supercritical kernels. In the pruned tree, a newborn survives as type $1$ only through a Bernoulli thinning whose parameter depends on the current type-$1$ age structure, and only type-$1$ individuals are counted as potential parents of type-$1$ offspring; thinning a predictable intensity multiplies it by the retention probability, giving $\lambda^1$. Since pruning only removes individuals, $N^1$ is dominated by the linear process $N$.

## Sources

- Manon Costa, Maxime Ligonnière, "A branching construction for nonlinear Hawkes processes – application to a case of infinite inhibition", arXiv (2026). Section 1 (Definition 1.1), Section 2 (CMJ construction, Theorem 2.1), Section 3 (hereditary types, Theorem 3.1, application to nonlinear Hawkes processes), Section 4 (inhibition examples). <https://doi.org/10.48550/arXiv.2611.34589>
