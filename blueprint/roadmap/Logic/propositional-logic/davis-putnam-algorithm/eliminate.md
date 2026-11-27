# Davis-Putnam elimination of a variable

Eliminating a variable $x$ from a CNF formula
$\varphi$ gives the formula consisting of the clauses of $\varphi$ that contain neither $x$ nor
$\neg x$, followed by the resolvents on $x$ of $C$ and $D$, for every clause $C$ of $\varphi$ that
contains $x$ but not $\neg x$ and every clause $D$ of $\varphi$ that contains $\neg x$ but not $x$.
Clauses containing both $x$ and $\neg x$ are dropped.
