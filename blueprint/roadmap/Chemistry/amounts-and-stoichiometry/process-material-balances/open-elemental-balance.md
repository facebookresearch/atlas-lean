# Open elemental balance

Let $A$ be a composition matrix, $A_{bs}$ the amount of element (or charge) $b$ in one formula unit of species $s$, and let $N$
be a stoichiometric matrix whose columns are reactions balanced for $A$, so $AN = 0$. Let the species amounts $n : I \to \mathbb{R}^S$
of an open reactor be differentiable on an interval $I$ with

$$n'(t) = F_{\mathrm{in}}(t) - F_{\mathrm{out}}(t) + N\,w(t),$$

for given stream flows $F_{\mathrm{in}}, F_{\mathrm{out}}$ and reaction rates $w$. Then the elemental amounts satisfy

$$\frac{d}{dt}\,A\,n(t) = A\bigl(F_{\mathrm{in}}(t) - F_{\mathrm{out}}(t)\bigr).$$

The same calculation applies to any constant real row $\ell^{\mathsf T}$ with $\ell^{\mathsf T}N=0$:
$(\ell^{\mathsf T}n)' = \ell^{\mathsf T}(F_{\mathrm{in}}-F_{\mathrm{out}})$. Element and charge rows are particular cases.

A closed reactor ($F_{\mathrm{in}} = F_{\mathrm{out}} = 0$) keeps $A n$ constant, and at a steady state the elements entering equal
the elements leaving, $A F_{\mathrm{in}} = A F_{\mathrm{out}}$. A source term that is not balanced changes the elemental totals: with
two species of one atom each, $A = (1\ \ 1)$, the fictitious reaction $A \to 2B$, $\nu = (-1, 2)$, has $A\nu = 1 \ne 0$.

## Depends on

- [Balanced reaction for a composition matrix](../balanced-reactions-and-stoichiometric-conservati/is-balanced.md)

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.36 (species balance with production rates, p. 127); Exercise 2.8, Equation 2.67, the element balance $\nu A = 0$ (pp. 58–59), written there with the transposed composition matrix.
