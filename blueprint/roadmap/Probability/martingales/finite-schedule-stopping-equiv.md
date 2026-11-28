# Stopping-time equivalence on a finite schedule

Let $(\mathcal F_t)_{t\in J}$ be a filtration on a measurable space $\Omega$, where $J$ is linearly ordered. Let $e:\{0,\ldots,n\}\to J$ be strictly increasing and let $(\mathcal G_k)$ be the [sampled filtration](finite-schedule-filtration.md). Define $\mathcal I$ to consist of the stopping indices $i:\Omega\to\{0,\ldots,n\}$ for $\mathcal G$, and $\mathcal S$ to consist of the stopping times $\tau:\Omega\to J$ for $\mathcal F$ whose values lie in the range of $e$.

The finite-schedule equivalence $E:\mathcal I\simeq\mathcal S$ is defined by applying $e$ pointwise. Its defining equation is

$$(E(i))(\omega)=e(i(\omega)).$$

For $\tau\in\mathcal S$, the inverse $E^{-1}(\tau)$ sends each $\omega$ to the unique index $j$ such that $e(j)=\tau(\omega)$.
