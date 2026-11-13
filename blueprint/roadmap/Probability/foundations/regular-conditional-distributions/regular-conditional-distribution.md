# Regular conditional distribution (measure-valued family)

Let $P$ be a measure on a
measurable space $(\Omega, \mathcal{F})$, let $S$ be a measurable space, $X : \Omega \to S$ a
map, $\mathcal{G}$ a σ-algebra on $\Omega$, and $\rho$ a family assigning a measure $\rho_\omega$
on $S$ to each $\omega \in \Omega$. Then $\rho$ is a regular conditional distribution of $X$
given $\mathcal{G}$ under $P$ if $\mathcal{G} \subseteq \mathcal{F}$; $X$ is
$\mathcal{F}$-measurable; for every measurable $A \subseteq S$ the map
$\omega \mapsto \rho_\omega(A)$ is $\mathcal{G}$-measurable; $\rho_\omega(S) \le 1$ for every
$\omega$; for every measurable $A \subseteq S$ the real number $\rho_\omega(A)$ agrees, for
$P$-almost every $\omega$, with the conditional expectation
$P[\mathbf{1}_{X^{-1}(A)} \mid \mathcal{G}](\omega)$; and $\rho_\omega$ is a probability measure
for $P$-almost every $\omega$.

Because each $\rho_\omega$ is a measure, countable additivity holds at every sample point,
including null ones; this is stricter than the raw set-function definition of Lecture 26, whose
set functions need to form probability measures only almost everywhere.
