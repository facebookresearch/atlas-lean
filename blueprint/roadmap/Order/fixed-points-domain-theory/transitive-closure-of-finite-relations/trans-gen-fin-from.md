# Elements reachable from a finite set of sources

Let $\alpha$ be a finite type with
decidable equality, let $r$ be a decidable relation on $\alpha$, and let $A \subseteq \alpha$ be a
finite set. Write $\mathrm{post}_r(Z)$ for the set of $r$-successors of elements of a finite set
$Z \subseteq \alpha$, and let $f$ be the step map
$f(Z) = \mathrm{post}_r(A) \cup \mathrm{post}_r(Z)$. The finite set of elements reachable from
$A$ is $f^{|\alpha|}(\emptyset)$, obtained by applying $f$ to the empty set $|\alpha|$ times,
where $|\alpha|$ is the number of elements of $\alpha$.

Since $f$ is monotone, this is the least fixed point of $f$; it consists of the elements
reachable from some element of $A$ in one or more $r$-steps.
