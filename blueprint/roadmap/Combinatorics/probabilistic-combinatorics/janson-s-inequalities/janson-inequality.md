# First Janson inequality

Let $R$ be a random subset of a finite set that contains each element $a$ independently with probability $p(a)$, let $S_1, \dots, S_k$ be subsets and $A_i = \{S_i \subseteq R\}$. With [μ](janson-mu.md) $= \sum_i \Pr[A_i]$ and [Δ](janson-delta.md) the sum of $\Pr[A_i \cap A_j]$ over ordered pairs $i \neq j$ with $S_i \cap S_j \neq \emptyset$,

$$\Pr[\text{no } A_i \text{ occurs}] \le e^{-\mu + \Delta/2}.$$

When $\Delta = o(\mu)$ and every $\Pr[A_i] = o(1)$ this matches the Harris lower bound $\prod_i (1 - \Pr[A_i]) = e^{-(1+o(1))\mu}$. For triangles in $G(n, p)$ it gives $\Pr[G(n,p) \text{ is triangle-free}] \le e^{-(1+o(1)) \binom n3 p^3}$ for $p = o(n^{-1/2})$.

Zhao's Setup 7.10 chooses each element independently; the proof there (Boppana–Spencer with Warnke's modification) uses the Harris inequality for independent boolean variables and so covers element-dependent probabilities $p(a)$.

## Informally uses

- [Harris inequality](../../../Probability/correlation-inequalities/harris-fkg-bk/harris-inequality/harris-inequality.md): conditioning the increasing event $A_i \cap \bigcup_{j < i, j \sim i} A_j$ on the decreasing event "no non-neighbour $A_j$ occurs" can only lower its probability.

## Background

- [Second moment method for counts of events](../first-and-second-moment-methods/measure-real-forall-not-mem-le.md): the polynomial bound $(\mu + \Delta)/\mu^2$ for the same probability.

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Theorem 7.11; originally Svante Janson, Tomasz Łuczak and Andrzej Ruciński (1990).
