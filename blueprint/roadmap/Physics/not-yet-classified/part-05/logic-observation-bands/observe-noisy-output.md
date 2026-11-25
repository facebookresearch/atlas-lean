# Noisy logic output is observed as the intended bit

Let $V_{ol} < V_{il} < V_{ih} < V_{oh}$ and let $b$ be a Boolean value. Let $y$ be a voltage with $y \le V_{ol}$ if $b$ is false and $y \ge V_{oh}$ if $b$ is true, and let the noise $e$ satisfy

$$|e| < \min(V_{il} - V_{ol},\ V_{oh} - V_{ih}).$$

Then the observation of $y + e$ with thresholds $V_{il}, V_{ih}$ (false if $\le V_{il}$, otherwise true if $\ge V_{ih}$, otherwise undefined) equals $b$.
