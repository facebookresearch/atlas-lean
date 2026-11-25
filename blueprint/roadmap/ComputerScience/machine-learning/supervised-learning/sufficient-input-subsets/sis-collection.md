# SIS-collection procedure

Let $g$ be a real function on the finite subsets of a set of features, $\tau \in \mathbb{R}$ and
$\pi$ a rule choosing an element of every nonempty finite set. The SIS-collection from a finite set
$R$ is defined recursively: if $\tau \le g(R)$ and [FindSIS](find-sis.md) from $R$ returns a
nonempty set $S$, it is $S$ followed by the SIS-collection from $R \setminus S$; otherwise it is
empty. So while the remaining features are sufficient, it finds a SIS among them, records it and
masks it; it stops if FindSIS returns the empty set (only possible when $\tau \le g(\emptyset)$).
