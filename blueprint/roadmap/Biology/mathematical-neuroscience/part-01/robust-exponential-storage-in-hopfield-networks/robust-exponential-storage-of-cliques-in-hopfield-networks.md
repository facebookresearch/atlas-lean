# Robust exponential storage of cliques in Hopfield networks

**Hopfield network.** On states $x \in \{0,1\}^n$ take a real symmetric weight matrix $W$ with zero diagonal and thresholds $\theta \in \mathbb{R}^n$, with energy $E_x = -\tfrac12 x^\top W x + \theta^\top x$. The asynchronous dynamics replaces, neuron by neuron, $x_e$ by $1$ if $\sum_{f\neq e} W_{ef}x_f > \theta_e$ and by $0$ otherwise. With $I_e = \sum_f W_{ef}x_f$, each update changes energy by $\Delta E_e = -\Delta x_e\,(I_e - \theta_e) \le 0$, so every initial state converges in finitely many steps to a fixed point (attractor).

**Robustness.** For $p \in [0,\tfrac12]$ the $p$-corruption $x^{p}$ of $x$ flips each bit independently with probability $p$. An attractor $x^*$ is $(1-\varepsilon)$-tolerant to $p$-corruption if the dynamics started at $(x^*)^{p}$ returns to $x^*$ with probability at least $1-\varepsilon$; $\alpha(X,\varepsilon)$ is the largest $p$ that every state of $X$ tolerates in this sense. A sequence of networks $H_n$ storing $X_n$ has robustness index

$$\alpha = \lim_{\varepsilon \to 0^+} \lim_{n \to \infty} \inf\{\alpha(X_n,\varepsilon), \alpha(X_{n+1},\varepsilon), \dots\} \;\le\; \tfrac12 .$$

**Clique networks.** Let $n = \binom{v}{2}$, one neuron per edge of the complete graph on $v$ vertices, so states are graphs; a $k$-clique is the graph of all edges among $k$ vertices. In the three-parameter family, $W_{ef} = x$ if edges $e,f$ share one vertex, $W_{ef} = y$ if they are disjoint, and $\theta_e = z$; the energy of a graph $G$ is

$$E_G = -x\,S_1(G) - y\,S_0(G) + z\,\#E(G),$$

with $S_1, S_0$ the numbers of edge pairs of $G$ sharing exactly one, respectively no, vertex.

**Theorem (robust exponential storage).** Take $v = 2k$, $y=0$, $z=1$, and for a fixed $p<\tfrac12$

$$x = \frac{3+2p}{4k(1+2p)} .$$

Then a $p$-corrupted $k$-clique is restored with probability tending to $1$ as $k \to \infty$, in a single parallel update. Hence there are Hopfield networks on $n=\binom{2k}{2}$ neurons that robustly store all

$$\binom{2k}{k} \sim \frac{2^{\sqrt{2n}+\frac34}}{n^{1/4}\sqrt{\pi}}$$

$k$-cliques with the maximal robustness index $\alpha = \tfrac12$. The source prints the exponent as $\sqrt{2n}+\tfrac14$; since $n = k(2k-1)$ gives $2k = \tfrac12 + \sqrt{2n} + o(1)$, Stirling's $\binom{2k}{k}\sim 4^k/\sqrt{\pi k}$ gives $\tfrac34$, and the printed form is off by the factor $\sqrt2$.

**Minimum probability flow.** For training patterns $X$ the probability-flow objective

$$K(W,\theta) = \frac{1}{|X|}\sum_{x\in X}\sum_{x' \in N(x)} \exp\Bigl(\frac{E_x - E_{x'}}{2}\Bigr),$$

with $N(x)$ the states at Hamming distance one from $x$, is convex in $(W,\theta)$, and $X$ consists of attractors iff $K$ can be made arbitrarily small. Over all $k$-cliques with $v = 2k-2$ and the three-parameter family with fixed $z>0$, $K$ is minimized uniquely at $(x,0,z)$ with $x = 2z/(3k-5)$; this network stores all $k$-cliques with robustness index $\tfrac14$. Gradient descent on $K$ for one pattern gives the local learning rule $\Delta W_{ef} \propto -x_f\,\Delta x_e\,e^{-\Delta E_e/2}$, $\Delta\theta_e \propto \Delta x_e\,e^{-\Delta E_e/2}$.

## Expansion

In a $p$-corrupted $k$-clique on $2k$ vertices, Bernstein's inequality shows that with high probability every clique edge has about $2k$ present neighbouring edges and every non-clique edge touching the clique has at most about $k(1+2p)$; disjoint edges do not matter when $y=0$. A clique edge is switched on iff its input exceeds $z$ and a non-clique edge is switched off iff its input is at most $z$, so storage of the corrupted clique in one update requires $2kx > z \ge k(1+2p)x$ up to lower-order terms. The choice $x = 2z/(3k-5) \approx 2z/(3k)$ meets this for $p<\tfrac14$, while choosing $x$ halfway between $z/(2k)$ and $z/(k(1+2p))$ meets it for every $p<\tfrac12$. The capacity is exponential in $\sqrt n$ while each neuron has only $O(\sqrt n)$ nonzero inputs, and the basins have radius proportional to $n$ in expected Hamming distance.

## Sources

- C. J. Hillar, N. M. Tran, "Robust Exponential Memory in Hopfield Networks", Journal of Mathematical Neuroscience (2018), Background (Eqs. (2)–(5)), Sect. 3 (Eqs. (6)–(8), Theorems 1–2), Sect. 5 (Proposition 1, Corollary 1, proofs of Theorems 1–2), <https://doi.org/10.1186/s13408-017-0056-2>, PMCID PMC5770423.
