# Invalid observation of a voltage between the logic thresholds

For real thresholds $V_{il}$ and $V_{ih}$, a voltage $v$ is an invalid observation when its
[three-valued observation](../logic-levels-and-noise-margins/observe.md) is `none`. For
$V_{il} < V_{ih}$ this means that $v$ lies strictly between the thresholds, $V_{il} < v < V_{ih}$
([invalid band](../logic-levels-and-noise-margins/observe-eq-none-iff.md)); for $V_{ih} \le V_{il}$
no voltage is invalid.
