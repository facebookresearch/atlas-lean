# Three-valued observation of a voltage against logic thresholds

For real thresholds $V_{il}$ and $V_{ih}$, the observation of a voltage $v \in \mathbb{R}$ is

- low, the value `some false`, if $v \le V_{il}$;
- otherwise high, the value `some true`, if $v \ge V_{ih}$;
- otherwise invalid, the value `none`.

The low test comes first. For $V_{il} < V_{ih}$, the intended ordering of the input thresholds, a
voltage is therefore observed low for $v \le V_{il}$, invalid in the open band
$V_{il} < v < V_{ih}$, and high for $v \ge V_{ih}$: at each threshold the observation is that
threshold's Boolean value, and a voltage inside the band is not coerced to a Boolean value. For
$V_{ih} \le V_{il}$ there is no invalid band: every $v \le V_{il}$ is observed low, even when
$v \ge V_{ih}$, and every $v > V_{il}$ is observed high.
