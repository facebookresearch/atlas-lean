# The ancestral line count with recombination is positive recurrent

Let $K$ be the continuous-time Markov chain on $\{1, 2, \dots\}$ that jumps from $k$ to $k + 1$ at rate $\rho k/2$ (a recombination splits a line) and to
$k - 1$ at rate $\binom k2$ (two lines coalesce), with $\rho \ge 0$.

- **$\rho > 0$.** Detailed balance $\pi_{k+1}/\pi_k = (\rho k/2)/\binom{k+1}{2} = \rho/(k+1)$ gives the summable solution $\pi_k \propto \rho^k/k!$, the Poisson($\rho$) law conditioned on $k \ge 1$. The chain is irreducible, and it does not explode because the birth rates are linear. It is therefore positive recurrent with stationary law $\pi$. The birth–death formula $\mathbb E_k T_{k-1} = \bigl(\binom k2 \pi_k\bigr)^{-1} \sum_{j \ge k} \pi_j$ gives, from two lines,

$$\mathbb E_2 T_1 = \frac{2(e^\rho - 1 - \rho)}{\rho^2}, \qquad \mathbb E_2 \int_0^{T_1} K_s\, ds = \frac{2(e^\rho - 1)}{\rho},$$

and the expected number of recombinations before $T_1$ is $\frac\rho2 \cdot \frac{2(e^\rho - 1)}{\rho} = e^\rho - 1$, since recombinations occur at rate $\rho K/2$.
- **$\rho = 0$.** The chain is a pure death process: every $k > 1$ is transient and $1$ is absorbing. From $n$ lines, the absorption time is the time to the most recent common ancestor of Kingman's coalescent, with
[mean](../kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md) $2(1 - 1/n)$.

As $\rho \to 0$ the three values for two lines tend to $1$, $2$ and $0$.

## Related topics

- [States of the two-locus ancestral process](two-locus-state.md)
- [Expected time to the most recent common ancestor](../kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md)

## Sources

- R. C. Griffiths, "The two-locus ancestral graph", in *Selected Proceedings of the Sheffield Symposium on Applied Probability*, IMS Lecture Notes 18 (1991), 100–117. The stationary law and the two-line values are derived above and checked against a truncated linear system at $\rho = 0.5, 1, 2$.
