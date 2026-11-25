# FindSIS procedure for sufficient input subsets

Let $g$ be a real function on the finite subsets of a set of features, $\tau \in \mathbb{R}$ a
threshold and $\pi$ a rule choosing an element of every nonempty finite set. FindSIS from a finite
set $R$ un-masks features in reverse order of masking: it runs through the
[backward-selection chain](chain.md) $R_0 = R, \dots, R_{|R|} = \emptyset$ backwards, starting from
$\emptyset$, and returns the first set $R_t$ with $\tau \le g(R_t)$, or no set if there is none.
