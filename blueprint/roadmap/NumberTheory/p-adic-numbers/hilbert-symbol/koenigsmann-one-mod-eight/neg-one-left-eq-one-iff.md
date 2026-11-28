# The Hilbert symbol $(-1, b)_\ell$ at an odd prime

Let $\ell$ be an odd prime and let
$b \in \mathbb{Q}_\ell$ be nonzero. Then $(-1, b)_\ell = 1$ if and only if $\ell \equiv 1 \pmod 4$
or the $\ell$-adic valuation $v_\ell(b)$ is even.

This is the case $a = -1$ of the formula for the Hilbert symbol at an odd prime
(`padicHilbertSymbol.eq_formula_of_ne_two`): writing $b = \ell^\beta v$ with
$\beta = v_\ell(b)$ and $v$ a unit of $\mathbb{Z}_\ell$, it gives
$(-1, b)_\ell = \left(\frac{-1}{\ell}\right)^\beta$, and
$\left(\frac{-1}{\ell}\right) = \chi_4(\ell)$ (`legendreSym.at_neg_one`), which is $1$ for
$\ell \equiv 1 \pmod 4$ and $-1$ for $\ell \equiv 3 \pmod 4$. It is the step
"These two conditions imply $(-1,q)_l = 1$" of the proof of Proposition 16(a) of J. Koenigsmann,
"Defining $\mathbb{Z}$ in $\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93, p. 85, in a form for
every nonzero $\ell$-adic $b$; `padicHilbertSymbol.neg_one_left_eq_one_of_rat` states it as
Koenigsmann uses it.
