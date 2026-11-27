# Aggregate junction conservation

Let links $E$ and commodities $C$ be finite, each link $e$ run from junction $\mathrm{tail}(e)$ to junction $\mathrm{head}(e)$, and let $q_c(e, e')$ be the turning flow of commodity $c$ from link $e$ to link $e'$. If $q_c(e, e') = 0$ whenever $\mathrm{head}(e) \ne \mathrm{tail}(e')$, then at every junction $v$

$$\sum_{\mathrm{head}(e) = v} \sum_{c} \sum_{e'} q_c(e, e') = \sum_{\mathrm{tail}(e) = v} \sum_{c} \sum_{e_0} q_c(e_0, e).$$

No sign condition on the flows is needed, and nothing is said about first-in first-out order between commodities.
