# Simulating the variable-size coalescent by a time change

Tavaré (2004, Section 2.4, Algorithm 2.1) simulates the holding times $T^v_n, \dots, T^v_2$ of the coalescent of a sample of size $n$ under a deterministic size history with positive, locally integrable intensity $\lambda$ and integrated intensity $\Lambda(t) = \int_0^t \lambda(u)\,du$ satisfying $\Lambda(t) \to \infty$ as $t \to \infty$ (his Section 2.4 assumptions), so that $\Lambda$ is a continuous increasing bijection of $[0, \infty)$ and $\Lambda^{-1}$ is an ordinary inverse, as follows: draw independent uniform variables $U_n, \dots, U_2$ on $(0, 1)$, set $t_j = -2\log(U_j)/(j(j - 1))$, form the partial sums $s_n = t_n$ and $s_j = t_j + \dots + t_n$, and return $T^v_n = \Lambda^{-1}(s_n)$ and $T^v_j = \Lambda^{-1}(s_j) - \Lambda^{-1}(s_{j+1})$. Since $t_j$ is exponential with rate $\binom j2$, the $t_j$ are the constant-size holding times, and the output has the law of the variable-size holding times by the time-change representation $T^v_j = \Lambda^{-1}(S_j) - \Lambda^{-1}(S_{j+1})$ (equation (2.4.9)); Algorithm 2.2 is the sequential version. The unbounded cumulative rate is needed: for the relative population size $\eta(t) = e^t$, so that $\lambda(t) = 1/\eta(t) = e^{-t}$, one has $\Lambda(t) = 1 - e^{-t} < 1$, and with two lineages the exponential draw $s_2$ lies outside the range of $\Lambda$ with probability $e^{-1}$, so the genealogy never completes with that probability; such histories are covered only with an explicit convention, such as an infinite holding time. Exact simulators of the coalescent generate events by waiting times computed from the current state rather than by stepping through generations (Kelleher, Etheridge and McVean 2016, section "Efficient coalescent simulation"), using the exponential race: when events of types $j$ occur at rates $a_j$, the waiting time to the next event is exponential with rate $a_0 = \sum_j a_j$, and the type is $j$ with probability $a_j/a_0$, independently of the waiting time ([competing exponential clocks](../../../../Probability/distributions/continuous/exponential-distribution/competing-exponential-clocks.md)); the stochastic simulation algorithm of Gillespie (1977) is built on the same rule, cited here as background. The statement is about the algorithm on exact real numbers and exact uniform variables; pseudorandom numbers and floating-point evaluation of $\Lambda^{-1}$ are separate matters.

## Depends on

- [Clock and epoch lengths of the variable-size coalescent](../../site-frequency-spectrum-under-variable-populatio/deterministic-coalescent-time-change.md)
- [Cumulative coalescence intensity](../../site-frequency-spectrum-under-variable-populatio/cum-rate.md)
- [Competing exponential clocks](../../../../Probability/distributions/continuous/exponential-distribution/competing-exponential-clocks.md)

## Expansion

1. The exponential race: the minimum of independent exponential clocks, its rate, and the independent choice of the clock that rings first.
2. Algorithm 2.1: exactness of $-2\log(U)/(j(j - 1))$ as an exponential variable, and of the time-changed partial sums as the variable-size holding times when $\Lambda(t) \to \infty$; for bounded $\Lambda$, the generalized inverse with value $+\infty$ and the resulting incomplete genealogies, as a separate statement.
3. The sequential Algorithm 2.2, and the combination with a uniformly random merging pair at each event to produce the full genealogy.
4. Mutation placement as a Poisson process on the branches given the genealogy.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Section 2.4, Algorithms 2.1 and 2.2, equation (2.4.9).
- J. Kelleher, A. M. Etheridge and G. McVean, Efficient coalescent simulation and genealogical analysis for large sample sizes, PLoS Comput. Biol. 12 (2016), e1004842, section "Efficient coalescent simulation". <https://doi.org/10.1371/journal.pcbi.1004842>
- D. T. Gillespie, Exact stochastic simulation of coupled chemical reactions, J. Phys. Chem. 81 (1977), 2340–2361. <https://doi.org/10.1021/j100540a008>
