# Flag $h$-vector

Let $P$ be a finite partially ordered set with a grade function
$\rho \colon P \to \mathbb{Z}_{\ge 0}$, that is, $\rho(s) < \rho(t)$ whenever $s < t$,
$\rho(t) = \rho(s) + 1$ whenever $t$ covers $s$, and $\rho(t) = 0$ whenever $t$ is minimal. Let
$\alpha_P$ be the flag $f$-vector of $P$ with respect to $\rho$: for a finite set
$T \subseteq \mathbb{Z}_{\ge 0}$, $\alpha_P(T)$ is the number of maximal chains in the subposet
$\{t \in P : \rho(t) \in T\}$. The flag $h$-vector of $P$ is the integer-valued function $\beta_P$
on finite sets $S \subseteq \mathbb{Z}_{\ge 0}$ given by

$$\beta_P(S) = \sum_{T \subseteq S} (-1)^{|S \setminus T|} \alpha_P(T),$$

where the sum runs over all subsets $T$ of $S$ and $|S \setminus T|$ is the number of elements of
$S \setminus T$. In particular, $\beta_P(\emptyset) = \alpha_P(\emptyset) = 1$.
