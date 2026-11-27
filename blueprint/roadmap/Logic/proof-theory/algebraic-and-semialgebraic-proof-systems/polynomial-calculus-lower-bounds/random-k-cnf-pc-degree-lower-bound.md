# Random k-CNF formulas require linear polynomial calculus degree over every field

For fixed $k \ge 3$ and clause density $\Delta$ not too large, a random $k$-CNF with $\Delta n$ clauses requires polynomial calculus refutations of degree $\Omega(n/(\Delta^{2/(k-2)} \log \Delta))$ over every field, including characteristic $2$, with probability $1 - o(1)$.

Let $F \sim \mathcal{F}^k_{n,\Delta}$ denote a random $k$-CNF on $n$ variables with $\Delta n$ clauses, each picked independently and uniformly, with repetitions, from the $\binom{n}{k} 2^k$ clauses of width $k$.

**Theorem.** Let $k \ge 3$ be a fixed integer and $\Delta = \Delta(n)$ a parameter with $\Delta \le o(n^{(k-2)/2})$. Then, with probability $1 - o(1)$, every polynomial calculus refutation of $F \sim \mathcal{F}^k_{n,\Delta}$ over an arbitrary field has degree

$$
\Omega\left( \frac{n}{\Delta^{2/(k-2)} \cdot \log \Delta} \right) .
$$

## Proof sketch

Ben-Sasson and Impagliazzo had proved an $\Omega(n)$ degree bound for random 3-CNFs over fields of characteristic different from $2$ with binomial techniques and conjectured the same in characteristic $2$; the non-binomial method settles it. A random $\Delta n \times n$ matrix whose rows are independent random $k$-subsets of $[n]$ is, with probability $1 - o(1)$, an $(\Omega(n/\Delta^{2/(k-c-2)}), k, c)$-expander for any $0 < c < k - 2$ when $\Delta = o(n^{(k-c-2)/2})$. Each clause polynomial has maximal immunity, so the degree lower bound $rc/2$ for maximal immunity on expanders applies; choosing $c = 1/\ln(\Delta + 2)$ gives the stated bound. For constant $k$ and constant $\Delta$ the degree bound is linear in $n$, so the size-degree relation turns it into an $\exp(\Omega(n))$ size lower bound for polynomial calculus resolution.

## Depends on

- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)
- [Polynomial calculus](../polynomial-calculus.md)

## Proof depends on

- [Polynomial calculus degree lower bounds for immune polynomials on expanders](pc-degree-lower-bound-for-immune-expander-systems.md)

## Sources

- Michael Alekhnovich, Alexander A. Razborov, "Lower bounds for polynomial calculus: non-binomial case", *42nd IEEE Symposium on Foundations of Computer Science (FOCS 2001)*, 2001, https://doi.org/10.1109/SFCS.2001.959893; theorem numbering of the authors' full version dated September 27, 2000 (Definition 4.7, Lemma 4.1, Theorem 3.13, Corollary 4.8).
