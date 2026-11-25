# For $V_{il}<V_{ih}$, a voltage is invalid exactly in $(V_{il},V_{ih})$

Let $V_{il} < V_{ih}$. The [observation](observe.md) of a voltage $v$ is invalid, the value `none`,
if and only if $V_{il} < v < V_{ih}$: the invalid band is the open interval between the thresholds,
and at both thresholds the observation is a Boolean value.
