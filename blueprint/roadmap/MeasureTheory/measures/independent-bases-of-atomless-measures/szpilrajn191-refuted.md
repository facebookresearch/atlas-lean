# Szpilrajn's Problem 191 has a negative answer

The claim of Szpilrajn's Problem 191 is false:
not every convex measure possesses a base. That is, there are a measurable space $X$ and a convex
measure $\mu$ on $X$ such that no class of subsets of $X$ is a base of $\mu$.

By Maharam's theorem, a non-atomic (convex) measure has a base exactly when its measure algebra is
homogeneous, that is, isomorphic to the measure algebra of a product $\{0, 1\}^\kappa$ with the fair
coin-tossing measure; every measure algebra is a countable sum of homogeneous ones, of possibly
different Maharam types $\kappa$. So a sum of two homogeneous pieces of different types gives a
counterexample: for instance, with weights $\frac12$ each, Lebesgue measure on $[0, 1]$ (type
$\aleph_0$) and the coin-tossing measure on $\{0, 1\}^I$ for an uncountable set $I$ (type $|I|$).

## Sources

- E. Szpilrajn, Problem 191 of the Scottish Book; the sets `B n` of numbers in `[0, 1]` whose `n`-th binary digit is `1` form a base for Lebesgue measure on `[0, 1]`. See the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
- D. Maharam, *On homogeneous measure algebras*, Proc. Nat. Acad. Sci. U.S.A. 28 (1942), 108–111.
- P. Borodulin-Nadzieja and M. Džamonja, *On the isomorphism problem for measures on Boolean algebras*,
  arXiv:1105.1250v1, introduction (Maharam's theorem and its decomposition into homogeneous pieces).
