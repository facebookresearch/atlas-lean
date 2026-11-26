# Switching-step bound for bipartite network rewiring

Let $B = (S, D, E)$ be a bipartite network with $t = |S||D|$ possible edges and density $d = |E|/t$, rewired by the switching algorithm of [Functional-connectivity-preserving rewiring via bipartite networks](functional-connectivity-preserving-rewiring-via-bipartite-networks.md). Let $x^{(k)}$ be the number of edges shared by $B$ and its rewired version after $k$ switching steps, and $\bar x$ its expected value once the switching chain is at stationarity. The number of steps $N$ is chosen so that $|x^{(k)} - \bar x| \le \epsilon$ for $k \ge N$. With $p_r$ the probability that a switching step succeeds,

$$N = \frac{|E|(1 - d)}{2p_r}\,\ln\!\left(\frac{|E|}{\epsilon} - \frac{|E|^2}{\epsilon t}\right).$$

Under a uniform degree distribution $p_r = (1-d)^2$, and the bound becomes

$$N = \frac{|E|}{2(1 - d)}\,\ln\!\left(\frac{|E|}{\epsilon} - \frac{|E|^2}{\epsilon t}\right), \qquad\text{which for } \epsilon = 1 \text{ is } N = \frac{|E|}{2(1-d)}\ln\big[(1 - d)|E|\big].$$

An absolute tolerance of one edge is a relative error below $0.01\%$ for $|E| > 10\,000$ but $1\%$ for $|E| = 100$. Writing the tolerance as a relative error $\delta$, $\epsilon = |E|\delta$, gives a bound linear in the number of edges:

$$N = \frac{|E|(1-d)}{2p_r}\,\ln\frac{1-d}{\delta}, \qquad\text{and for } p_r = (1-d)^2,\quad N = \frac{|E|}{2(1 - d)}\ln\frac{1 - d}{\delta}.$$

The default $\delta = 5 \times 10^{-5}$ corresponds to one edge when $|E| \approx 20\,000$.

**Similarity of signed networks.** For two DSNs $G = (V, E)$ and $\mathcal{H} = (V, F)$ with $|E| = |F|$ and $x = |E \cap F|$, the Jaccard index is

$$J(G, \mathcal{H}) = \frac{|E \cap F|}{|E \cup F|} = \frac{x}{2|E| - x}.$$

**Proposition (minimal Jaccard similarity).** If $R^+$ and $R^-$ are obtained from the positive and negative bipartite networks $B^+, B^-$ of $G$ by $N^+$ and $N^-$ switching steps computed from the $\delta$-form bound for each, then $J(G, f^{-1}(R^+, R^-))$ is (asymptotically) minimized.

## Depends on

- [Functional-connectivity-preserving rewiring via bipartite networks](functional-connectivity-preserving-rewiring-via-bipartite-networks.md)

## Expansion

The general bound can be read as the time for an exponential approach of the overlap to its stationary value: setting

$$x^{(k)} - \bar x \approx (|E| - \bar x)\exp\!\left(-\frac{2p_r\,k}{|E|(1-d)}\right), \qquad \bar x = \frac{|E|^2}{t} = d|E|,$$

equal to $\epsilon$ and solving for $k$ gives the displayed $N$, since $|E| - \bar x = |E|(1 - d)$; here $\bar x = d|E|$ is the expected overlap when each original edge is present in a random network with probability $d$. The substitution $\epsilon = |E|\delta$ cancels $|E|$ inside the logarithm, so $N = \Omega_\delta |E|$ with $\Omega_\delta = (1-d)(\ln(1-d) - \ln\delta)/(2p_r)$ depending only on density, tolerance and success probability.

For the proposition, $f^{-1}$ maps common positive edges to common edges of $B^+$ and $R^+$ and likewise for negative edges, so $x = x^+ + x^-$. Each step count drives its own overlap to its minimum, and $J = x/(2|E| - x)$ is increasing in $x$, so $J$ is minimized as well.

## Sources

- F. Iorio, M. Bernardo-Faura, A. Gobbi, T. Cokelaer, G. Jurman and J. Saez-Rodriguez, "Efficient randomization of biological networks while preserving functional characterization of individual nodes", BMC Bioinformatics 17 (2016), 542, Methods (Switching-algorithm lower bound for bipartite networks of any size, Eqs. 1–4; Convergence criteria for signed directed networks, Proposition 2), <https://doi.org/10.1186/s12859-016-1402-1> (PMC5168876).
