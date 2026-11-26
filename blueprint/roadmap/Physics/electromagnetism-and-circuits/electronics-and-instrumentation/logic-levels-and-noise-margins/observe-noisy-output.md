# Noise below both noise margins preserves the observed output bit

Let $V_{ol} < V_{il} < V_{ih} < V_{oh}$, let $b$ be an expected output bit, and let the ideal output
voltage $y$ encode it: $y \le V_{ol}$ if $b$ is false and $y \ge V_{oh}$ if $b$ is true. If additive
noise $e$ satisfies

$$|e| < \min\bigl(V_{il} - V_{ol},\ V_{oh} - V_{ih}\bigr),$$

below both noise margins, then the [observation](observe.md) of the noisy output $y + e$ is
`some b`, the expected bit. No gate function is modelled: the hypothesis on $y$ states directly that
the ideal output voltage encodes $b$. The result combines the [low side](observe-noisy-low.md) and
the [high side](observe-noisy-high.md).
