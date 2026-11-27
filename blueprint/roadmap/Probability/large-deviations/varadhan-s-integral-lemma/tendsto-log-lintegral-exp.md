# Varadhan's integral lemma

Let $X$ be a topological space with a $\sigma$-algebra containing the open sets, and let the
measures $(\mu_n)$ on $X$ satisfy the large deviation principle with rate function $I$. For every
continuous bounded $F : X \to \mathbb{R}$,

$$\lim_{n \to \infty} \frac{1}{n} \log \int_X e^{n F(x)} \, d\mu_n(x) = \sup_{x \in X} \bigl(F(x) - I(x)\bigr)$$

in the extended reals.

This is the Laplace method for large deviation principles: the integral is dominated by the
neighbourhood of the point maximising $F - I$. It expresses the Legendre duality between
logarithmic moment generating functions and rate functions, as in Cramér's theorem, where
$\log E[e^{\theta X}]$ and the rate function are Legendre transforms of each other.

The lower bound is local and needs only lower semicontinuity of $F$ and no boundedness
(Varadhan's Remarks 2.9 and 2.10). For the upper bound Varadhan uses superexponential tightness,
which requires a good rate function on a Polish space; the proof here instead covers $X$ by the
finitely many closed sets $F^{-1}[a_j, a_{j+1}]$ and applies the closed-set upper bound to each,
so the rate function need not be good.

## Background

- [Legendre transform](../legendre-transform/README.md): the duality that the lemma expresses at
  the level of measures.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 2, Theorem 2.8 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf). The upper bound follows the finite-partition argument of A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 4.3.
