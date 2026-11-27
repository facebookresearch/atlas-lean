# Values of the extended simply typed lambda calculus

A term is a value exactly when it is
a lambda abstraction, the unit value $\langle\rangle$, a pair of values, a left or right injection
of a value, or one of the boolean constants $\mathsf{tt}$ and $\mathsf{ff}$. These are the value
rules of the eager dynamics: rules (8.5a), (10.2a,b), (11.2b,c) and (11.6a,b) of Harper's
*Practical Foundations for Programming Languages*, 2nd ed. None of the rules produces a term of
base type.
