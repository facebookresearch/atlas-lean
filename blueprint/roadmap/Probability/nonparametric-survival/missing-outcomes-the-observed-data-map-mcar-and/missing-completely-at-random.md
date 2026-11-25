# Missing completely at random

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event, and $X : \Omega \to \mathcal X$, $Y : \Omega \to \mathcal Y$ covariate and outcome with values in measurable spaces. The outcome is missing completely at random (MCAR, Rubin 1976) if the response indicator $\mathbf 1_R$ is independent of the full data $(X, Y)$ under $\mu$: for every measurable $A \subseteq \{0,1\}$ and every measurable $t \subseteq \mathcal X \times \mathcal Y$,

$$\mu\bigl(\{\mathbf 1_R \in A\} \cap \{(X, Y) \in t\}\bigr) = \mu(\mathbf 1_R \in A)\, \mu\bigl((X, Y) \in t\bigr).$$
