# Packing and covering bounds for multiclass Natarajan classes

Let $C$ be a class of functions $X \to \beta$ with $\beta$ finite of size $k$, N-shattering no finite set of more than $d$ points, let $x \in X^m$ with $m \ge 1$ and $0 < \varepsilon \le 1$. Every set $P$ of realized labelings of $x$ whose distinct members differ in at least $\varepsilon m$ coordinates satisfies

$$
|P| \le \Big(\frac{8\max(1, \binom{k}{2})}{\varepsilon}\Big)^{2d},
$$

independent of $m$, and the realized labelings admit a Hamming net of radius $\varepsilon m$ of at most that size. For $k = 2$ this is Dudley's binary bound $(8/\varepsilon)^{2d}$.

## Proof sketch

Run the subsampling argument of Dudley's bound: some $r$ positions with $2\ln|P| < \varepsilon r$ separate $P$, so $|P|$ is at most the number of realized labelings on $r$ points, bounded by Natarajan's lemma in the form $e^{r/T}(T\max(1, \binom{k}{2}))^d$ for every $T \ge 1$; take $T = 4/\varepsilon$.

## Depends on

- [N-shattering](../natarajan-dimension-and-the-natarajan-lemma/nshatters.md)
- [Dudley's packing bound for classes of bounded VC dimension](../packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)

## Proof depends on

- [Natarajan's lemma](natarajans-lemma.md)
- [Dudley's packing bound for classes of bounded VC dimension](../packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)

## Sources

- R. M. Dudley, "Central Limit Theorems for Empirical Measures", The Annals of Probability, 1978.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
