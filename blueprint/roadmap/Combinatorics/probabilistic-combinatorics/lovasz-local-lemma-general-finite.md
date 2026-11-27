# Lovász local lemma, general form

Let $P$ be a probability mass function on a finite set $\Omega$, let $(A_i)_{i \in I}$ be finitely many events and $G$ a graph on $I$ such that each $A_i$ is mutually independent of the family of events $A_j$ with $j$ neither $i$ nor a neighbour of $i$ (in the form $\Pr[A_i \cap \bigcap_{j \in S} A_j] = \Pr[A_i] \Pr[\bigcap_{j \in S} A_j]$ for all such sets $S$, as in the [symmetric local lemma](lovasz-local-lemma-symmetric-finite.md)). If there are $x_i \in [0, 1)$ with

$$\Pr[A_i] \le x_i \prod_{j \sim i} (1 - x_j) \quad \text{for all } i,$$

then

$$\Pr\Big[\bigcap_{i} \overline{A_i}\Big] \ge \prod_i (1 - x_i) > 0.$$

When the maximum degree is at most $d \ge 1$, taking $x_i = 1/(d+1)$ recovers the symmetric criterion $e p (d + 1) \le 1$; when $d = 0$, $x_i = p \le 1/e$ does. The asymmetric form is what applications need when the bad events have very different probabilities.

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Theorem 6.10, Definition 6.2, and the deduction of Theorem 6.9 after Theorem 6.10.
