# Mixed binomial process is a Poisson process

Let $\mu$ be a finite measure on a measurable space $E$ and let $\eta$ be distributed as the
[Poisson point process](poisson-point-process.md) with intensity $\mu$. Let $(A_i)_{i \in \iota}$
be a finite family of pairwise disjoint measurable subsets of $E$. Then the counts
$(\eta(A_i))_{i \in \iota}$ are independent and $\eta(A_i)$ has the Poisson law of mean
$\mu(A_i)$: the joint law of the counts is the product of these Poisson laws. So the mixed
binomial process is a Poisson process with intensity $\mu$ in the sense of Definition 3.1 of the
source.

## Sources

- G. Last and M. Penrose, *Lectures on the Poisson Process*, IMS Textbooks, Cambridge University
  Press, 2017, Proposition 3.5.
