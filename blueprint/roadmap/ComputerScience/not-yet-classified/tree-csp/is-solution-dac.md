# Directional arc consistency loses no solution

Let a binary constraint problem have a parent function on its variables such that every parent edge $(p, x)$ is an arc of the problem. If an assignment $\sigma$ is a solution within domains $\mathrm{dom}$ (each $\sigma(x) \in \mathrm{dom}(x)$ and every arc allows the pair of values), then $\sigma$ is still a solution within the domains returned by the directional arc consistency pass, which revises the domain of each variable's parent against that variable, processing the variables in reverse order.
