# Logic-level observation of a voltage

For thresholds $V_{il}$, $V_{ih}$ and a voltage $v$, the observation of $v$ is the partial Boolean value

$$\mathrm{obs}(v) = \begin{cases} \text{false} & \text{if } v \le V_{il},\\ \text{true} & \text{if } v > V_{il} \text{ and } V_{ih} \le v,\\ \text{undefined (none)} & \text{if } V_{il} < v < V_{ih}. \end{cases}$$
