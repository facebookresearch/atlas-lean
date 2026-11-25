# Event that one synchronizer observation is invalid

Let $V_{il}$ and $V_{ih}$ be real thresholds and $x_i(\omega)$ the observed voltage of observation
$i$ at an outcome $\omega$ of a sample space $\Omega$. The invalid event of an index $i$ is the set

$$\{\omega \in \Omega : x_i(\omega) \text{ is an invalid observation}\}$$

of outcomes at which the [observation](../logic-levels-and-noise-margins/observe.md) of
$x_i(\omega)$ is `none` ([invalid observation](invalid-observation.md)). For $V_{il} < V_{ih}$ it is
$\{\omega : V_{il} < x_i(\omega) < V_{ih}\}$. The set need not be measurable.
