# Sinha: (1+eps)-approximate matching relaxations need binom(n, alpha/eps) inequalities

There is an absolute constant $\alpha \in (0,1)$ such that for every even $n$, every $\varepsilon$ with $\tfrac2n \le \varepsilon \le 1$ and every polytope $K$ with $P_{\mathrm{M}}(n) \subseteq K \subseteq (1+\varepsilon)P_{\mathrm{M}}(n)$, the extension complexity of $K$ over $\mathbb{R}$ satisfies

$$
\mathrm{xc}(K) \ge \binom{n}{\lfloor \alpha/\varepsilon \rfloor}.
$$

Sinha states the bound as $\binom{n}{\alpha/\varepsilon}$ without specifying a rounding and assumes divisibility in the proof; since $\alpha/\varepsilon \le \alpha n/2 < n/2$ and $\binom{n}{a}$ increases in $a$ on $[0, n/2]$, the rounded-down form above is implied. This is tight up to the constant $\alpha$: the relaxation $K_\varepsilon$ that keeps the nonnegativity and degree constraints and only the odd-set constraints $x(E(U)) \le \tfrac{|U|-1}{2}$ with $|U| \le 1+\tfrac1\varepsilon$ uses $n^{O(1/\varepsilon)}$ inequalities.

## Proof sketch

By the factorization lemma it suffices to bound the nonnegative rank of a slack matrix of the pair $(P_{\mathrm{M}}(n), Q'_\varepsilon)$, where the outer polytope $Q'_\varepsilon \supseteq (1+\varepsilon)P_{\mathrm{M}}(n)$ keeps the degree constraints and the odd-set constraints $x(E(U)) \le (|U|+\beta-1)/2$ for $|U| \le 1+\beta/\varepsilon$, with a small constant $\beta$. Restricted to odd cuts and perfect matchings its entries are $(|\delta(U) \cap M|+\beta-1)/2$, a noisy, lopsided version of the unique disjointness matrix in which one party holds a set of size $\Theta(1/\varepsilon)$. Following Braun and Pokutta's common information method, a nonnegative factorization of rank $r$ yields a random variable with at most $r$ values that makes the row and column variables of the normalized matrix conditionally independent; Sinha shows, using the lopsided structure as in lopsided disjointness lower bounds, that any such variable must take at least $\binom{n}{\alpha/\varepsilon}$ values, first for lopsided unique disjointness and then for the noisy matching slack matrix.

## Depends on

- [Multiplicatively approximate relaxations of the matching polytope](approximate-polytope-relaxation.md)
- [Extended formulations and extension complexity](../extended-formulation.md)
- [Matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)

## Proof depends on

- [Dropping large odd-set constraints gives a (1+eps)-approximate matching relaxation](truncated-odd-set-relaxation.md)
- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)
- [Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions](nested-pair-factorization.md)
- [Nonnegative rank of a matrix](../../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- Makrand Sinha, "Lower Bounds for Approximating the Matching Polytope", SODA (2018), ECCC TR17-185, Theorems 1.2, 1.3 and 3.3, Section 3 and Section 4.4.
- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369.
- Gabor Braun, Sebastian Pokutta, "Common Information and Unique Disjointness", Algorithmica (2016), FOCS (2013).
