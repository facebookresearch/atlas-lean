# Exposure Probability

Let $U$ be a finite set of units, $\Omega$ a set of assignments, $\Delta$ a set of exposure values, and $e : U \times \Omega \to \Delta$ an exposure mapping, so $e_i(z)$ is the exposure of unit $i$ under assignment $z$. Let $p$ be a probability mass function (design) on $\Omega$. For a unit $i$ and an exposure $d$, the exposure probability $\pi_i(d)$ is the inclusion probability of $i$ in the random exposed set $E_d(z) = \{j : e_j(z) = d\}$ when $z \sim p$, that is, the total mass that the pushed-forward design on subsets of $U$ gives to the subsets containing $i$:

$$\pi_i(d) = \sum_{s \subseteq U,\ i \in s} p\bigl(\{z : E_d(z) = s\}\bigr).$$

For a finite set of assignments, $\pi_i(d) = p\bigl(\{z : e_i(z) = d\}\bigr)$ ([exposure probability as a sum over assignments](exposure-probability-eq-sum.md)).
