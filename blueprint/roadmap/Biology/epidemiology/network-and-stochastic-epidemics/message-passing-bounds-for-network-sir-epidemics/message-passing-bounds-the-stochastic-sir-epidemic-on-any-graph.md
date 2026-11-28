# Message passing bounds the stochastic SIR epidemic on any graph

Let $G = (V, E)$ be a locally finite graph (finite or countable) with neighbourhoods $N_i$. Each individual $i$ is initially infected, susceptible or recovered/vaccinated with probabilities $1 - y_i - z_i$, $z_i$, $y_i$. If infected, $i$ has infectious period $\mu_i$ and makes contact with neighbour $j$ at time $\omega_{ji}$ after its infection, and the contact is infectious if $\omega_{ji} < \mu_i$. Assume:
- for each $i$ the family $\{-\mu_i\} \cup \{\omega_{ji} : j \in N_i\}$ is **associated**, i.e. $E[f g] \ge E[f]\,E[g]$ for all non-decreasing $f, g$ of these variables (independence is a special case);
- these families are mutually independent over $i$ and independent of the initial states.

Let $f_{ij}(\tau)$ be the density of the time, measured from $j$'s infection, at which $j$ makes an infectious contact to $i$, and let $r_i$ be the density of $\mu_i$. The **message-passing system** is

$$F_{i\leftarrow j}(t) = 1 - \int_0^t f_{ij}(\tau)\Bigl(1 - y_j - z_j \prod_{k \in N_j\setminus i} F_{j\leftarrow k}(t - \tau)\Bigr)d\tau,$$

$$S^{(i)}_{\mathrm{mes}}(t) = z_i \prod_{j \in N_i} F_{i\leftarrow j}(t), \qquad R^{(i)}_{\mathrm{mes}}(t) = y_i + \int_0^t r_i(\tau)\bigl[1 - y_i - S^{(i)}_{\mathrm{mes}}(t - \tau)\bigr]d\tau,$$

where $F_{i\leftarrow j}(t)$ approximates the probability that $i$, held in the cavity state (unable to transmit), has received no infectious contact from $j$ by time $t$.

**Theorem 1 (well-posedness).** If degrees are bounded and $\sup_{(i,j)}\sup_\tau f_{ij}(\tau) < \infty$, there is a unique feasible solution ($F_{i\leftarrow j} \in [0,1]$), and each feasible $F_{i\leftarrow j}$ is continuous and non-increasing.

**Theorem 2 (bounds).** For all $t \ge 0$ and $i \in V$,

$$P(i \text{ susceptible at } t) \ge S^{(i)}_{\mathrm{mes}}(t), \qquad P(i \text{ recovered at } t) \le R^{(i)}_{\mathrm{mes}}(t),$$

with equality when $G$ is a tree or forest. Summing over $i$, message passing gives an upper bound on the expected epidemic size at every time.

**Theorem 3 (cycles inhibit spread).** In the homogeneous model with bounded contact-time density, $\sup_{\tau \ge 0} f(\tau) < \infty$, on an $n$-regular arc-transitive graph, with i.i.d. individual behaviour, the probability that an individual is susceptible at time $t$ is smallest, and the probability that it is recovered is largest, on the $n$-regular Bethe lattice (infinite tree).

## Expansion

In the true process the event that $i$ escapes infection from $j$ depends on whether $j$ escapes from its other neighbours, and these escape events are positively correlated through shared ancestors on cycles. Association of each individual's contact and recovery times and the Harris–FKG inequality give $P(\cap_j \text{no infection from } j) \ge \prod_j P(\text{no infection from } j)$, which is the direction of Theorem 2. On a tree the cavity events are independent and the inequality is an equality. Theorem 3 follows by combining the bound on a general symmetric graph with exactness on the Bethe lattice, whose message-passing system is the same. With Poisson contacts at rate $\beta$ independent of recovery, the homogeneous message-passing system is equivalent to a closed pairwise model in $[S], [I], [SS], [SI]$ with a general infectious period, so that pairwise model also never underestimates the expected epidemic size.

## Sources

- R. R. Wilkinson, F. G. Ball, K. J. Sharkey, "The relationships between message passing, pairwise, Kermack–McKendrick and stochastic SIR epidemic models", Journal of Mathematical Biology (2017), Section 2, Eqs. (1)–(6), Theorems 1–3, Corollary 1, Theorem 5 and Corollary 2, <https://doi.org/10.1007/s00285-017-1123-8>, PMCID PMC5641366.
