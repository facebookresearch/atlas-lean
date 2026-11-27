# Fitness-dependent transitions between amplification and suppression

**Moran process on a graph.** Let $G$ be a connected undirected graph on $V = \{1,\dots,N\}$ with degrees $d_i$ and $w_{ij} = 1/d_i$ for neighbours ($0$ otherwise). Mutants have fitness $r > 0$ and residents fitness $1$. The state is the set $S$ of mutant vertices, the total reproductive weight is $w_S(r) = r|S| + N - |S|$, and

$$P_{S,S\cup\{j\}}(r) = \frac{r\sum_{i\in S} w_{ij}}{w_S(r)},\qquad P_{S,S\setminus\{j\}}(r) = \frac{\sum_{i\notin S} w_{ij}}{w_S(r)}$$

(a reproducing individual is chosen proportionally to fitness and its offspring replaces a uniformly chosen neighbour). The fixation probabilities $\Phi_S(r)$ solve $\Phi_S = \sum_{S'}P_{S,S'}\Phi_{S'}$ with $\Phi_\emptyset = 0$, $\Phi_V = 1$, i.e. $(I - Q(r))\Psi(r) = c(r)$ on the $2^N - 2$ transient states, and $\Phi(r) = \frac1N\sum_i \Phi_{\{i\}}(r)$ is a rational function of $r$ with rational coefficients. For the well-mixed population

$$\Phi_0(r) = \frac{1 - r^{-1}}{1 - r^{-N}} = \frac{r^{N-1}}{r^{N-1} + \cdots + r + 1},$$

and $\Phi = \Phi_0$ iff $G$ is regular (isothermal). For $r > 1$, $G$ is an amplifier at $r$ if $\Phi(r) > \Phi_0(r)$ and a suppressor if $\Phi(r) < \Phi_0(r)$; a transition is a fitness $r_c > 1$ where $\Phi - \Phi_0$ changes sign.

**Results (exhaustive over all connected undirected graphs with $N \le 10$).**
1. Most non-regular graphs of order at most $7$ are amplifiers for all $r > 1$, and most of order $8$ to $10$ are amplifiers for $1 < r \le 10$ (the range evaluated for those orders, where apparent amplifiers may still turn into suppressors at larger $r$); but suppressors and transitions occur: among the $112$ graphs of order $6$, five are isothermal, exactly one (the $\ell_6$ graph) is a suppressor for all $r > 1$, and six are suppressors that become amplifiers at a unique critical fitness.
2. Among the $853$ graphs of order $7$, exactly three are suppressors for every $r > 1$, $52$ are suppressors with a unique transition to amplification, and three are amplifiers that become suppressors at a unique $r_c$ (approximately $4.98$, $6.37$ and $24.79$), so amplification under weak selection need not persist under strong selection even with frequency-independent fitness.
3. From order $8$ on there are graphs with two or more transitions (suppressor–amplifier–suppressor, amplifier–suppressor–amplifier, and triple transitions); hence the regime of a graph cannot in general be inferred from simulations over a bounded fitness range.
4. For the $\ell$-graphs $\ell_N^{n,m}$ (a clique $K_{N-2}$ together with two adjacent extra vertices, joined respectively to disjoint sets of $n$ and $m$ vertices of the clique), so that $\ell_6^{2,2} = \ell_6$, exact computation of $\ell_N^{2,2}$ for $7 \le N \le 15$ shows suppression up to a unique transition to amplification.

## Depends on

- [Isothermal theorem, "if" direction](../../isothermal-theorem-for-evolutionary-graph-dynami/average-fixation-eq-moran-fixation.md)

## Expansion

Multiplying each linear equation by $w_S(r)$ clears denominators, so $\Phi(r)$ is the ratio of two integer polynomials; it is recovered exactly by solving the system at enough rational values of $r$ and interpolating, which turns the sign of $\Phi - \Phi_0$ into a polynomial root count on $(1,\infty)$. The suppression mechanism in $\ell$-graphs and clique-wheels combines a dense core, where a mutant is quickly replaced, with sparse peripheral links that funnel replacements into the core, balancing the star-like amplification of hubs. Amplifiers that turn into suppressors (for example friendship cycles and friendship stars of order $7$) show that the comparison with the well-mixed population can reverse as the selective advantage grows.

## Sources

- F. Alcalde Cuesta, P. González Sequeiros, Á. Lozano Rojo, "Evolutionary regime transitions in structured populations", PLoS ONE 13(11):e0200670 (2018), Eqs (1)–(11), Table 1, Figs 1–7 and S1–S2 Tables, <https://doi.org/10.1371/journal.pone.0200670>, PMCID PMC6261048.
