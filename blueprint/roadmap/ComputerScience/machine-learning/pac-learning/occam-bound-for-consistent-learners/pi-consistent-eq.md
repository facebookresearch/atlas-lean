# A hypothesis survives $m$ independent examples with probability $(1 - \operatorname{error})^m$

Let $D$ be a probability distribution on labelled examples and $h$ a hypothesis whose disagreement
set $\{(x, y) : h(x) \ne y\}$ is measurable. Under the product distribution $D^m$ of $m$
independent examples,

$$D^m\{S : h(x_i) = y_i \text{ for all } i < m\} = (1 - \operatorname{error}_D(h))^m ,$$

where $S = ((x_i, y_i))_{i<m}$. The event is the product of $m$ copies of the agreement set.

Here $\operatorname{error}_D(h) = D\{(x, y) : h(x) \ne y\}$ is the 0-1 error of a hypothesis under a joint distribution $D$ on labelled examples, with values in $[0, 1]$, and $1 - \operatorname{error}_D(h)$ is computed in $[0, \infty]$.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Section 2.3.1, equation (2.8) and the line after it.
