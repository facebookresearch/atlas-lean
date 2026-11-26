# Double-sample symmetrization: ghost samples and coordinate swaps

Let $\mu$ be a $\sigma$-finite measure on a measurable space $Z$ and $m \ge 1$. For $\sigma \in \{0,1\}^m$ let $\mathrm{sw}_\sigma : Z^m \times Z^m \to Z^m \times Z^m$ exchange the $i$-th coordinates of the two samples for every $i$ with $\sigma_i = 1$.

1. Each $\mathrm{sw}_\sigma$ preserves $\mu^m \otimes \mu^m$.
2. For every measurable $J \subseteq Z^m \times Z^m$, $2^m (\mu^m \otimes \mu^m)(J) = \int \#\{\sigma : \mathrm{sw}_\sigma(z) \in J\}\, d(\mu^m \otimes \mu^m)(z)$. Hence, if $\mu$ is a probability measure and for every double sample $z$ at most $2^m K$ of the $2^m$ swaps of $z$ lie in $J$, then $(\mu^m \otimes \mu^m)(J) \le K$.
3. (Ghost sample.) For probability measures $\nu, \nu'$ on $Z^m$, a measurable $J$, a set $B \subseteq Z^m$ and $c \ge 0$: if $\nu'(\{T : (S, T) \in J\}) \ge c$ for every $S \in B$, then $c\,\nu(B) \le (\nu \otimes \nu')(J)$.

## Proof sketch

Swapping coordinates of a pair of i.i.d. samples is a product of coordinate transpositions, each preserving the product measure. Averaging the indicator of $J$ over all $2^m$ swaps and using invariance gives the identity in item 2, and the counting bound follows by integrating the pointwise bound. Item 3 is Tonelli's theorem applied to the indicator of $J$.

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- V. N. Vapnik and A. Ya. Chervonenkis, "On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities", Theory of Probability and Its Applications, 1971.
