# Offspring generating function of the continuous offspring-production model

Consider a multi-type branching process with types $i = 1, \dots, n$. An individual of type $i$ stays infectious for an $\mathrm{Exp}(\gamma)$ time, during which it produces type-$j$ infections at constant rate $r_{ij} \ge 0$. Write $\Lambda_i = \sum_j r_{ij}$ and $R_{ij} = r_{ij}/\gamma$ (the mean number of type-$j$ offspring). The probability generating function of the offspring vector of a type-$i$ individual is

$$F_i(\mathbf s) = \frac{\gamma}{\gamma + \sum_j r_{ij}(1 - s_j)} = \frac{1}{1 + \sum_j R_{ij}(1 - s_j)}, \qquad \mathbf s \in [0,1]^n .$$

The total number of offspring is geometric with mean $\sum_j R_{ij}$, and given the total the types are multinomial with probabilities $r_{ij}/\Lambda_i$. The extinction probabilities starting from one individual of each type form the least solution $\mathbf x \in [0,1]^n$ of $\mathbf x = \mathbf F(\mathbf x)$.

**Single type.** With $R_0 = r/\gamma$, $x = 1/(1 + R_0(1 - x))$ is equivalent to $(R_0x - 1)(x - 1) = 0$, so the extinction probability is $\min(1, 1/R_0)$ and the probability of emergence (non-extinction) is

$$P_{\mathrm{emerge}} = \max\Bigl(0,\ 1 - \frac{1}{R_0}\Bigr).$$

## Depends on

- [Generation sizes of the branching process](../branching-process-approximation-of-early-epidemi/bp-size.md)

## Expansion

While infectious, the individual faces competing exponential clocks: recovery at rate $\gamma$ and infection of type $j$ at rate $r_{ij}$. Each event is recovery with probability $\gamma/(\gamma + \Lambda_i)$, otherwise an infection of type $j$ with probability $r_{ij}/(\gamma + \Lambda_i)$, independently of the past by memorylessness. The offspring sequence is therefore a run of independent type draws stopped at the first recovery, whose generating function is $\sum_{m \ge 0}\bigl(\sum_j \tfrac{r_{ij}}{\gamma+\Lambda_i}s_j\bigr)^m \tfrac{\gamma}{\gamma+\Lambda_i}$, a geometric series that sums to $F_i$. This model matches event-driven stochastic simulations of SIS and SIR epidemics, unlike burst models with a fixed offspring law.

## Sources

- G. E. Leventhal, A. L. Hill, M. A. Nowak, S. Bonhoeffer, "Evolution and emergence of infectious diseases in theoretical and real-world networks", Nature Communications 6 (2015) 6101, Methods ("Branching process calculations for disease emergence in networks"), <https://doi.org/10.1038/ncomms7101> (PMC4335509).
