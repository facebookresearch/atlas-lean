# The complete dispersal graph is locally optimal

In the neutral [Moran process on two dispersal graphs](moran-process-on-two-dispersal-graphs.md), let $K_N$ be the complete graph and $M_N$ the graph obtained from $K_N$ by deleting one edge, $N \ge 3$. Then

$$\rho(M_N, K_N) = \frac{N-2}{(N-1)^2} \;<\; \frac1N = \rho(K_N, K_N),$$

so a mutant that loses a single dispersal edge against complete-graph residents is disfavoured, and

$$\rho(K_N, M_N) = \frac{N^2 - 2N + 2}{N(N-1)^2} \;>\; \frac1N,$$

so complete-graph mutants are favoured against residents that miss one edge. In this sense $K_N$ is a local maximum of $G \mapsto \rho(G, K_N)$ and a local minimum of $G \mapsto \rho(K_N, G)$.

## Depends on

- [Moran process on two dispersal graphs](moran-process-on-two-dispersal-graphs.md)

## Proof depends on

- [Absorption probabilities and mean times of a finite Markov chain](../../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Proof sketch

Call the two endpoints of the missing edge *special*. By symmetry the state is $(a, b)$: $a$ mutants among the $N-2$ ordinary sites and $b \in \{0,1,2\}$ among the special ones. For mutants on $M_N$ against residents on $K_N$, the function

$$\varphi(a,b) = \frac{(a+b)(N-2) + \tfrac12 b(b-1)}{(N-1)^2}$$

satisfies $\varphi(0,0) = 0$, $\varphi(N-2, 2) = 1$, and has zero expected one-step change: the four transition probabilities are $p_{b+} = \frac aN\cdot\frac{2-b}{N-1}$, $p_{a+} = \frac aN\cdot\frac{N-2-a}{N-1} + \frac bN\cdot\frac{N-2-a}{N-2}$, $p_{b-} = \frac{N-a-b}{N}\cdot\frac{b}{N-1}$, $p_{a-} = \frac{N-a-b}{N}\cdot\frac{a}{N-1}$, and the drift reduces to a multiple of $b(b-1)(b-2) = 0$. Hence $\varphi$ is the fixation probability, and $\varphi(1,0) = \varphi(0,1) = (N-2)/(N-1)^2$ gives the first formula. For mutants on $K_N$ against residents on $M_N$, the analogous solution is $\varphi(a,b) = [(a+b)(N-2) + \tfrac12 b(3-b)]/(N-1)^2$, so a mutant starting on a special site fixes with probability $\varphi(0,1) = 1/(N-1)$ and one starting on an ordinary site with probability $(N-2)/(N-1)^2$; the uniform average is $[(N-2)^2 + 2(N-1)]/(N(N-1)^2)$, which exceeds $1/N$ because $N^2 - 2N + 2 > (N-1)^2$. (The source's Theorem A.1 states $\rho(K_N, M_N) = 1/(N-1)$, which is the special-site value; the uniform average above follows from the same $\varphi$ and matches exact numerical solution of the absorption equations, e.g. $5/18$ for $N = 4$.)

## Sources

- J. Tkadlec, K. Kaveh, K. Chatterjee, M. A. Nowak, "Evolutionary dynamics of mutants that modify population structure", Journal of the Royal Society Interface (2023), <https://doi.org/10.1098/rsif.2023.0355> (PMC10684346).
