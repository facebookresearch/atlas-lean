# Lusin's theorem

Let $X$ be a locally compact Hausdorff space with its Borel $\sigma$-algebra and $\mu$ a finite
measure on $X$ that is regular: finite on compact sets, outer regular, and inner regular on open
sets by compact sets. Let $Y$ be a second-countable topological space with its Borel
$\sigma$-algebra and $f : X \to Y$ measurable. Then for every $\varepsilon > 0$ there is a compact
set $K \subseteq X$ with $\mu(X \setminus K) < \varepsilon$ such that the restriction of $f$ to $K$
is continuous.

## Idea

Measurable functions are nearly continuous: after removing a set of arbitrarily small measure,
what remains is continuous. The indicator of the rationals in $[0, 1]$ is continuous nowhere, yet
its restriction to the complement of a small open set containing the rationals is constant. For
the proof, take a countable base $(U_k)$ of $Y$; regularity approximates each preimage
$f^{-1}(U_k)$ from inside by a compact set and from outside by an open set, up to measure
$\varepsilon 2^{-k}$. On the set where all these approximations are exact, every
$f^{-1}(U_k)$ is relatively open, so $f$ is continuous there, and inner regularity shrinks that
set to a compact one.

## Statements

- [Lusin's theorem](lusin.md)

## Sources

- G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999.
