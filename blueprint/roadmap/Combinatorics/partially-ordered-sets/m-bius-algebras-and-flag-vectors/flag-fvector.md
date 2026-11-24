# Flag $f$-vector

Let $P$ be a finite partially ordered set with a grade function
$\rho \colon P \to \mathbb{Z}_{\ge 0}$, that is, $\rho(s) < \rho(t)$ whenever $s < t$,
$\rho(t) = \rho(s) + 1$ whenever $t$ covers $s$ (that is, $s < t$ and no $u \in P$ satisfies
$s < u < t$), and $\rho(t) = 0$ whenever $t$ is minimal. For a finite set
$S \subseteq \mathbb{Z}_{\ge 0}$, let $P_S = \{t \in P : \rho(t) \in S\}$. The flag $f$-vector of
$P$ is the function $\alpha_P$ on finite sets $S \subseteq \mathbb{Z}_{\ge 0}$ such that
$\alpha_P(S)$ is the number of maximal chains in $P_S$, that is, of subsets $C \subseteq P_S$ any
two elements of which are comparable and such that every element of $P_S \setminus C$ is
incomparable with some element of $C$. In particular $\alpha_P(\emptyset) = 1$, the empty chain
being the only maximal chain in the empty poset.
