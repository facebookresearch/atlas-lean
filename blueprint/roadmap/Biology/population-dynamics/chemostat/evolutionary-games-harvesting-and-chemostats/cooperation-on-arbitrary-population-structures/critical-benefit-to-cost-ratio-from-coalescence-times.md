# Critical benefit-to-cost ratio from coalescence times

**Setting.** A population of $N$ individuals occupies the vertices of a connected, undirected, weighted graph $G$ with weights $w_{ij} = w_{ji} \ge 0$ (self-loops allowed), $w_i = \sum_j w_{ij}$, $W = \sum_i w_i$. Random-walk steps have probabilities $p_{ij} = w_{ij}/w_i$, $n$-step probabilities $p^{(n)}_{ij}$, and stationary distribution $\pi_i = w_i/W$. Each individual is a cooperator, paying cost $c$ to give benefit $b$ to each neighbour (weighted by edge weight), or a defector. Under **death-Birth** updating, a random individual dies and neighbours compete for the vacancy with probability proportional to edge weight times fecundity $1 + \delta\cdot(\text{payoff})$, with selection strength $\delta \to 0$. Let $\tau_{ij}$ be the expected coalescence time of two random walkers started at $i$ and $j$,

$$\tau_{ij} = \begin{cases} 1 + \tfrac12\sum_k\big(p_{ik}\tau_{kj} + p_{jk}\tau_{ik}\big), & i \ne j,\\ 0, & i = j,\end{cases} \qquad \tau^{(n)} = \sum_{i,j}\pi_i\,p^{(n)}_{ij}\,\tau_{ij}.$$

**Theorem.** Starting from a single cooperator placed uniformly at random (and, more generally, under the corresponding mutant-appearance distribution), the fixation probability of cooperation is

$$\rho_C = \frac1N + \frac{\delta}{2N}\Big(-c\,\tau^{(2)} + b\big(\tau^{(3)} - \tau^{(1)}\big)\Big) + O(\delta^2),$$

so cooperation is favoured ($\rho_C > 1/N > \rho_D$ to first order) if and only if $-c\tau^{(2)} + b(\tau^{(3)} - \tau^{(1)}) > 0$, i.e. when $\tau^{(3)} > \tau^{(1)}$, if and only if

$$\frac{b}{c} > \Big(\frac{b}{c}\Big)^* = \frac{\tau^{(2)}}{\tau^{(3)} - \tau^{(1)}} .$$

These quantities are computed by solving a linear system of size $O(N^2)$, so the condition is decidable in polynomial time for every graph. For a weighted regular graph without self-loops with Simpson degree $\kappa = (\sum_j p_{ij}^2)^{-1}$, $(b/c)^* = (N-2)/(N/\kappa - 2)$.

**Theorem (meeting-time inequalities).** For any connected weighted graph, $\tau^{(1)} + \tau^{(2)} \ge \tau^{(3)}$, $\tau^{(2)} + \tau^{(3)} \ge \tau^{(1)}$ and $\tau^{(1)} + \tau^{(3)} \ge \tau^{(2)} + 2$, with equality in the first two exactly for two vertices without self-loops and in the third exactly for two vertices. Consequently, for $N \ge 3$, $|(b/c)^*| > 1$: no population structure lets cooperation succeed with $b/c \le 1$.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

At neutrality ($\delta = 0$) death-Birth updating is a voter model, whose genealogy is a system of coalescing random walks on $G$. To first order in $\delta$, the change in fixation probability equals the expected cumulative selective drift under the neutral process, which depends on the probability that individuals at two sites are identical by descent; these identity probabilities are expressed through the coalescence times $\tau_{ij}$. A cooperator's own cost enters through pairs at distance two (sites competing for the same vacancy) and benefits through pairs at distances one and three, which produces the combination $-c\tau^{(2)} + b(\tau^{(3)} - \tau^{(1)})$. The meeting-time inequalities follow from the recurrence for $\tau_{ij}$ together with the bound $1 + p^{(2)}_{ii} \ge 4\pi_i$.

## Sources

- Benjamin Allen, Gabor Lippner, Yu-Ting Chen, Babak Fotouhi, Naghmeh Momeni, Shing-Tung Yau et al., "Evolutionary dynamics on any population structure", Nature 544 (2017), 227–230, <https://doi.org/10.1038/nature21723>. Published version of arXiv:1605.06530, cited next; locators there refer to the arXiv version.
- Benjamin Allen, Gabor Lippner, Yu-Ting Chen, Babak Fotouhi, "Evolutionary dynamics on any population structure", arXiv (2016). Supplementary Sections A–E (model, coalescing random walks, fixation probability and condition for success, weighted regular graphs), Section H (Lemma 1, Theorem 1, Corollary 1). <https://doi.org/10.48550/arXiv.1605.06530>
