# MCAR as a discrete conditional independence

Let $\mu$ be a probability measure on a measurable space $\Omega$, $R \subseteq \Omega$ a measurable response event, and $X : \Omega \to \mathcal X$, $Y : \Omega \to \mathcal Y$ with values in measurable spaces. Then the outcome is missing completely at random ($\mathbf 1_R$ independent of $(X, Y)$) if and only if $R$ is discretely conditionally independent of $(X, Y)$ given a constant, that is, for every measurable $t \subseteq \mathcal X \times \mathcal Y$,

$$\mu\bigl(R \cap \{(X, Y) \in t\}\bigr)\, \mu(\Omega) = \mu(R)\, \mu\bigl((X, Y) \in t\bigr).$$
