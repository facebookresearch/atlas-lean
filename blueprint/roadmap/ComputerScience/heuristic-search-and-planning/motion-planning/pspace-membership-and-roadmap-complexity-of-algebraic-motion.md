# PSPACE membership and roadmap complexity of algebraic motion planning

This node collects upper bounds for motion planning with semialgebraic configuration spaces, with the input
parameters of the instance definition (dimension $n$ of configuration space, number $m$ of polynomials, maximal degree $d$,
coefficient bit-length).

## Expansion

A sound expansion has separate pages for:

1. **PSPACE membership** (Canny): the generalized mover's problem with polynomial constraints with rational coefficients is in
   PSPACE, so with the hardness results it is PSPACE-complete.
2. **Cylindrical algebraic decomposition** decides it in time $(md)^{O(1)^n}$: polynomial in $m$ and $d$ for each fixed $n$, and
   doubly exponential in $n$.
3. **Canny's roadmap algorithm** decides it in time $m^n (\log m)\, d^{O(n^4)}$, singly exponential in $n$, and a randomized
   variant in randomized expected time $m^n (\log m)\, d^{O(n^2)}$.

## Depends on

- [Semi-algebraic motion planning instances and input size](semi-algebraic-motion-planning-instances-and-input-size.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Planning Algorithms, web section 'General algorithms' (Ch. 6 computational complexity) — S. M. LaValle, Planning Algorithms, General algorithms (node306), Sec. 6.5.3: the bounds $(md)^{O(1)^n}$ and $m^n (\lg m)\, d^{O(n^4)}$, and $m^n (\lg m)\, d^{O(n^2)}$ randomized expected. <http://www.lavalle.pl/planning/node306.html>
- Planning Algorithms, web section 'Lower bounds for motion planning' (Ch. 6 computational complexity) — S. M. LaValle, Planning Algorithms, Canny's PSPACE membership, Sec. 6.5.1. <https://lavalle.pl/planning/node303.html>
