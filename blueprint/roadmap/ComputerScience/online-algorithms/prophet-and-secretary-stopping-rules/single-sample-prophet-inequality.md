# Single-sample prophet inequality

Let $X_0, \dots, X_{n-1}$ be independent nonnegative random variables with laws $\mu_0, \dots, \mu_{n-1}$ unknown to the gambler, who instead sees one independent sample $s_i \sim \mu_i$ of each law in advance. Draw a uniform permutation $\pi$ of $2n$ slots, give sample $j$ rank $\pi(2j)$ and online step $i$ rank $\pi(2i+1)$, and accept the first online value $X_i$ such that $(X_i, \pi(2i+1))$ exceeds $(s_j, \pi(2j))$ lexicographically for every $j$ (that is, $X_i$ beats the sample maximum, ties broken by the random ranks). Then

$$
\mathbb{E}\bigl[\max_i X_i\bigr] \le 2\,\mathbb{E}[\text{reward}],
$$

for every arrival order of the online values, with no integrability assumption. Without random tie-breaking the guarantee fails: if $X_0 = 1$ deterministically, accepting only values strictly above $\max_j s_j$ collects $0$.

## Proof sketch

Pair each sample with its online value and flip a fair coin for which member of each pair is the sample (deferred decisions). Among the $2n$ pooled values, the rule collects the overall maximum whenever it falls on the online side and the second maximum on the sample side, and a counting argument over coin assignments (an explicit two-to-one injection) gives the factor $2$. Random ranks make all pooled values distinct in the lexicographic order.

## Depends on

- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Proof depends on

- [Samuel-Cahn's median-threshold prophet inequality and optimality of 1/2](samuel-cahn-median-prophet-inequality.md)

## Sources

- Aviad Rubinstein, Jack Z. Wang and S. Matthew Weinberg, "Optimal Single-Choice Prophet Inequalities from Samples", 11th Innovations in Theoretical Computer Science Conference (ITCS), 2020.
