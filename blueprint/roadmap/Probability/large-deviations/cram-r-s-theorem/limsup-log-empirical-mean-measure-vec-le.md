# Cramér upper bound for closed sets

Let $X_0, X_1, \dots$ be independent, identically distributed random vectors in $\mathbb{R}^d$ with
$E[e^{\langle t, X_0 \rangle}] < \infty$ for every $t$, and let $\mu_n$ be the law of the empirical
mean $\frac1n \sum_{i<n} X_i$. For every closed set $F \subseteq \mathbb{R}^d$,

$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(F) \le -\inf_{x \in F} \Lambda^*(x),$$

which is the upper-bound half of Cramér's theorem in exactly the form required by the large
deviation principle.

Proof: for each $x$ and $q < \Lambda^*(x)$ pick $t$ with $\langle t, x \rangle - \Lambda(t) > q$; the open
half-space where $\langle t, \cdot \rangle - \Lambda(t) > q$ contains $x$ and has $\mu_n$-mass at most
$e^{-nq}$ by the Chebyshev (Chernoff) bound. Finitely many such half-spaces cover a compact set.
Chernoff bounds in the $2d$ coordinate directions give exponential tightness, which passes from
compact to closed sets.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 1 and Exercise 2 there (https://math.nyu.edu/~varadhan/LDP/1-2.pdf): Chebyshev's inequality in half-spaces and a covering argument; see also A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2.
